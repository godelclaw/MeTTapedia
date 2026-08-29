#!/usr/bin/env python3
"""Clear literal rational denominators from a Singular lift certificate.

The strict checker intentionally rejects division.  Singular can nevertheless
print a valid Q-coefficient identity using literal coefficients such as 1/2.
This converter accepts division only between signed integer literals, computes
the exact polynomial multipliers over Q, clears one global denominator, and
then asks the unchanged strict checker to replay the resulting integer identity.

No divided variable or divided polynomial is accepted.  The output proves
``sum multiplier_i * equation_i = d`` for a nonzero integer ``d``.
"""

from __future__ import annotations

import os
import argparse
import ast
import hashlib
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

from strict_certificate_checker import (  # noqa: E402
    CertificateError,
    check_c4,
    framed_body,
    load_json_strict,
    symbols_for,
    validate_variable_names,
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def signed_integer_literal(node: ast.AST) -> int | None:
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        value = signed_integer_literal(node.operand)
        if value is None:
            return None
        return value if isinstance(node.op, ast.UAdd) else -value
    return None


def rational_poly_from_ast(
    node: ast.AST,
    symbol_map: dict[str, sp.Symbol],
    symbols: tuple[sp.Symbol, ...],
) -> sp.Poly:
    if isinstance(node, ast.Expression):
        return rational_poly_from_ast(node.body, symbol_map, symbols)
    literal = signed_integer_literal(node)
    if literal is not None:
        return sp.Poly(literal, *symbols, domain=sp.QQ)
    if isinstance(node, ast.Name):
        if node.id not in symbol_map:
            raise CertificateError(f"undeclared multiplier symbol: {node.id}")
        return sp.Poly(symbol_map[node.id], *symbols, domain=sp.QQ)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        value = rational_poly_from_ast(node.operand, symbol_map, symbols)
        return value if isinstance(node.op, ast.UAdd) else -value
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Div):
            numerator = signed_integer_literal(node.left)
            denominator = signed_integer_literal(node.right)
            if numerator is None or denominator is None:
                raise CertificateError(
                    "division is allowed only between signed integer literals"
                )
            if denominator == 0:
                raise CertificateError("zero denominator in rational literal")
            value = Fraction(numerator, denominator)
            return sp.Poly(sp.Rational(value.numerator, value.denominator),
                           *symbols, domain=sp.QQ)
        left = rational_poly_from_ast(node.left, symbol_map, symbols)
        if isinstance(node.op, ast.Pow):
            exponent = signed_integer_literal(node.right)
            if exponent is None or exponent < 0:
                raise CertificateError("power exponent must be a nonnegative integer literal")
            return left ** exponent
        right = rational_poly_from_ast(node.right, symbol_map, symbols)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.Sub):
            return left - right
        if isinstance(node.op, ast.Mult):
            return left * right
        raise CertificateError(f"disallowed multiplier operator: {type(node.op).__name__}")
    raise CertificateError(
        "disallowed multiplier syntax: " + ast.dump(node, include_attributes=False)
    )


def parse_rational_multiplier(
    text: str, symbols: tuple[sp.Symbol, ...]
) -> sp.Poly:
    source = text.strip().replace("^", "**")
    try:
        tree = ast.parse(source, mode="eval")
    except SyntaxError as exc:
        raise CertificateError(f"invalid multiplier syntax: {exc}") from exc
    table = {str(symbol): symbol for symbol in symbols}
    return rational_poly_from_ast(tree, table, symbols)


def coefficient_denominator_lcm(polynomials: list[sp.Poly]) -> int:
    result = 1
    for polynomial in polynomials:
        for coefficient in polynomial.coeffs():
            denominator = int(sp.denom(coefficient))
            result = math.lcm(result, denominator)
    return result


def strict_integer_text(polynomial: sp.Poly, denominator: int) -> str:
    scaled = polynomial.mul_ground(denominator)
    for coefficient in scaled.coeffs():
        if sp.denom(coefficient) != 1:
            raise CertificateError("global denominator did not clear every coefficient")
    integer = scaled.set_domain(sp.ZZ)
    return str(integer.as_expr()).replace("**", "^")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    system = load_json_strict(args.system)
    names = validate_variable_names(system.get("variables"))
    symbols = symbols_for(names)
    equation_count = len(system.get("equations", []))
    lines = args.input.read_text(encoding="utf-8").splitlines()

    basis_lines = [line.strip() for line in framed_body(
        lines, "C4_LIFT_BASIS_BEGIN", "C4_LIFT_BASIS_END") if line.strip()]
    if len(basis_lines) != 1:
        raise CertificateError(f"expected one basis element, got {len(basis_lines)}")
    basis = parse_rational_multiplier(basis_lines[0], symbols)
    if basis.is_zero or basis.total_degree() != 0:
        raise CertificateError("basis element must be a nonzero rational constant")

    body = framed_body(lines, "C4_LIFT_CERTIFICATE_BEGIN", "C4_LIFT_CERTIFICATE_END")
    if len(body) != 3 * equation_count:
        raise CertificateError(
            f"certificate body has {len(body)} lines; expected {3 * equation_count}"
        )
    multipliers: list[sp.Poly] = []
    for offset in range(0, len(body), 3):
        if body[offset] != "C4_LIFT_ENTRY":
            raise CertificateError(f"missing entry marker at body line {offset}")
        expected_index = len(multipliers) + 1
        if body[offset + 1].strip() != str(expected_index):
            raise CertificateError(f"certificate index drift at {expected_index}")
        multipliers.append(parse_rational_multiplier(body[offset + 2], symbols))

    denominator = coefficient_denominator_lcm([basis, *multipliers])
    scaled_basis = basis.mul_ground(denominator)
    if scaled_basis.total_degree() != 0 or scaled_basis.is_zero:
        raise CertificateError("scaled basis is not a nonzero constant")
    basis_value = int(scaled_basis.as_expr())

    output_lines = [
        "C4_LIFT_BASIS_BEGIN",
        str(basis_value),
        "C4_LIFT_BASIS_END",
        "C4_LIFT_SHAPE",
        str(equation_count),
        "1",
        "C4_LIFT_CHECK_BEGIN",
        str(basis_value),
        "C4_LIFT_CHECK_END",
        "C4_LIFT_CERTIFICATE_BEGIN",
    ]
    for index, multiplier in enumerate(multipliers, start=1):
        output_lines.extend([
            "C4_LIFT_ENTRY",
            str(index),
            strict_integer_text(multiplier, denominator),
        ])
    output_lines.append("C4_LIFT_CERTIFICATE_END")
    args.output.write_text("\n".join(output_lines) + "\n", encoding="utf-8")

    verdict = check_c4(args.system, args.output)
    result = {
        "denominator_lcm": denominator,
        "input_certificate_sha256": digest(args.input),
        "output_certificate_sha256": digest(args.output),
        "strict_replay": verdict,
    }
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
