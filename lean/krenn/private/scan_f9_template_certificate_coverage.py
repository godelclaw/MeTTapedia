#!/usr/bin/env python3
"""Exact coverage scan for recurring compact f9 certificate templates.

This performs no Gröbner computation.  Each candidate case is reconstructed
import os
from the original f9 generator, and already strict-replayed multiplier
templates are substituted into that case's ordered frozen equations.  A case
is reported only when the exact Q-polynomial sum is the nonzero constant one.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

import freeze_f9_case  # noqa: E402
from strict_certificate_checker import (  # noqa: E402
    CertificateError,
    check_c4,
    framed_body,
    parse_multiplier,
)


ROW = re.compile(r"\[case (\d+) .*\] nodes=(\d+) .* -> CLOSED")
SUPPORT = "01,02,03,04,15"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def multiplier_texts(certificate: Path, equation_count: int) -> list[str]:
    lines = certificate.read_text(encoding="utf-8").splitlines()
    body = framed_body(lines, "C4_LIFT_CERTIFICATE_BEGIN", "C4_LIFT_CERTIFICATE_END")
    if len(body) != 3 * equation_count:
        raise CertificateError("template certificate equation-count drift")
    values: list[str] = []
    for offset in range(0, len(body), 3):
        expected = len(values) + 1
        if body[offset] != "C4_LIFT_ENTRY" or body[offset + 1].strip() != str(expected):
            raise CertificateError(f"template certificate index drift at {expected}")
        values.append(body[offset + 2])
    return values


def multiplier_tree(text: str) -> ast.Expression:
    """Parse a multiplier without constructing its multivariate polynomial."""
    try:
        tree = ast.parse(text.strip().replace("^", "**"), mode="eval")
    except SyntaxError as exc:
        raise CertificateError(f"invalid multiplier syntax: {exc}") from exc
    if not isinstance(tree, ast.Expression):  # pragma: no cover - mode="eval"
        raise CertificateError("multiplier did not parse as an expression")
    return tree


def evaluate_multiplier(node: ast.AST, values: dict[str, Fraction]) -> Fraction:
    """Evaluate exactly, accepting precisely the strict checker's AST grammar."""
    if isinstance(node, ast.Expression):
        return evaluate_multiplier(node.body, values)
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return Fraction(node.value)
    if isinstance(node, ast.Name):
        if node.id not in values:
            raise CertificateError(f"undeclared multiplier symbol: {node.id}")
        return values[node.id]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        value = evaluate_multiplier(node.operand, values)
        return value if isinstance(node.op, ast.UAdd) else -value
    if isinstance(node, ast.BinOp):
        left = evaluate_multiplier(node.left, values)
        if isinstance(node.op, ast.Pow):
            if not isinstance(node.right, ast.Constant) or type(node.right.value) is not int:
                raise CertificateError("power exponent must be a literal integer")
            exponent = node.right.value
            if exponent < 0:
                raise CertificateError("power exponent must be nonnegative")
            return left ** exponent
        right = evaluate_multiplier(node.right, values)
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


def main() -> int:
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--log", type=Path)
    source.add_argument("--case-manifest", type=Path)
    parser.add_argument("--template", type=Path, action="append", required=True)
    parser.add_argument("--template-system", type=Path, action="append", required=True)
    parser.add_argument("--pending-only", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if len(args.template) != len(args.template_system):
        raise ValueError("every template requires its source system")
    if args.pending_only and args.case_manifest is None:
        raise ValueError("--pending-only requires --case-manifest")

    cases: dict[int, int] = {}
    case_inventory_manifest_sha256: str | None = None
    if args.log is not None:
        historical_log_sha256 = digest(args.log)
        for line in args.log.read_text(encoding="utf-8").splitlines():
            match = ROW.search(line)
            if match is not None:
                case, nodes = map(int, match.groups())
                if case in cases:
                    raise ValueError(f"duplicate historical closure row: {case}")
                cases[case] = nodes
    else:
        manifest = json.loads(args.case_manifest.read_text(encoding="utf-8"))
        if manifest.get("format") != "krenn-f9-legacy-migration-v1":
            raise ValueError("case manifest has the wrong format")
        if manifest.get("historical_closed_count") != 317:
            raise ValueError("case manifest does not bind 317 historical closures")
        if manifest.get("support") != [[0, 1], [0, 2], [0, 3], [0, 4], [1, 5]]:
            raise ValueError("case manifest has the wrong support")
        rows = manifest.get("cases")
        if not isinstance(rows, list) or len(rows) != 317:
            raise ValueError("case manifest does not contain 317 case rows")
        for row in rows:
            case = row.get("case_index")
            nodes = row.get("historical_trace_nodes")
            if not isinstance(case, int) or not isinstance(nodes, int):
                raise ValueError("case manifest has a malformed historical row")
            if args.pending_only and row.get("migration_status") != \
                    "pending_compact_certificate":
                continue
            if case in cases:
                raise ValueError(f"duplicate case-manifest row: {case}")
            cases[case] = nodes
        historical_log_sha256 = manifest.get("historical_log_sha256")
        if not isinstance(historical_log_sha256, str) or not re.fullmatch(
            r"[0-9a-f]{64}", historical_log_sha256
        ):
            raise ValueError("case manifest has no valid historical-log digest")
        case_inventory_manifest_sha256 = digest(args.case_manifest)
    expected_cases = (
        manifest.get("pending_count")
        if args.case_manifest is not None and args.pending_only
        else 317
    )
    if not isinstance(expected_cases, int) or len(cases) != expected_cases:
        raise ValueError(
            f"expected {expected_cases} cases in selected scope, got {len(cases)}"
        )

    templates: list[dict[str, object]] = []
    for certificate, system in zip(args.template, args.template_system, strict=True):
        verdict = check_c4(system, certificate)
        system_data = json.loads(system.read_text(encoding="utf-8"))
        names = system_data.get("variables")
        if not isinstance(names, list) or not all(isinstance(name, str) for name in names):
            raise ValueError("template system has a malformed variable inventory")
        texts = multiplier_texts(certificate, verdict["equations"])
        selected = [index for index, text in enumerate(texts) if text.strip() != "0"]
        templates.append({
            "certificate": certificate,
            "certificate_sha256": digest(certificate),
            "texts": texts,
            "selected": selected,
            "trees": [(index, multiplier_tree(texts[index])) for index in selected],
            "evaluated_by_inventory": {},
            "parsed_by_inventory": {},
        })

    # Deterministic exact evaluation is a fail-safe negative prefilter.  If a
    # proposed polynomial identity evaluates to something other than one at
    # this rational point, it cannot be the constant polynomial one.  Pairs
    # that happen to evaluate to one still undergo the original full exact
    # polynomial calculation, so this optimization can never create a hit or
    # discard a genuine identity.
    evaluation_values = [2, 3, 5, 7, 11]

    rows: list[dict[str, object]] = []
    counts = [0] * len(templates)
    prefilter_rejected = 0
    exact_pairs = 0
    incompatible_pairs = 0
    for ordinal, (case, nodes) in enumerate(sorted(cases.items()), start=1):
        symbols_list, equations_expr, _metadata = freeze_f9_case.reconstruct(
            SUPPORT, case, None, None
        )
        symbols = tuple(symbols_list)
        equations = [sp.Poly(value, *symbols, domain=sp.QQ) for value in equations_expr]
        evaluation_point = {
            symbol: evaluation_values[index % len(evaluation_values)]
            for index, symbol in enumerate(symbols)
        }
        inventory = tuple(str(symbol) for symbol in symbols)
        rational_point = {
            name: Fraction(evaluation_values[index % len(evaluation_values)])
            for index, name in enumerate(inventory)
        }
        equation_values = [equation.eval(evaluation_point) for equation in equations]
        hits: list[int] = []
        for template_index, template in enumerate(templates):
            evaluation_cache = template["evaluated_by_inventory"]
            if inventory not in evaluation_cache:
                try:
                    evaluation_cache[inventory] = [
                        (index, evaluate_multiplier(tree, rational_point))
                        for index, tree in template["trees"]
                    ]
                except CertificateError:
                    evaluation_cache[inventory] = None
            evaluated_multipliers = evaluation_cache[inventory]
            if evaluated_multipliers is None:
                incompatible_pairs += 1
                continue
            evaluated = sum(
                equation_values[index] * multiplier
                for index, multiplier in evaluated_multipliers
            )
            if evaluated != 1:
                prefilter_rejected += 1
                continue
            exact_pairs += 1
            parse_cache = template["parsed_by_inventory"]
            if inventory not in parse_cache:
                try:
                    parse_cache[inventory] = [
                        (index, parse_multiplier(template["texts"][index], symbols))
                        for index in template["selected"]
                    ]
                except CertificateError:
                    parse_cache[inventory] = None
            parsed = parse_cache[inventory]
            if parsed is None:
                incompatible_pairs += 1
                exact_pairs -= 1
                continue
            value = sp.Poly(0, *symbols, domain=sp.QQ)
            for index, multiplier in parsed:
                value += equations[index] * multiplier
            if value == sp.Poly(1, *symbols, domain=sp.QQ):
                hits.append(template_index)
                counts[template_index] += 1
        rows.append({
            "case_index": case,
            "historical_trace_nodes": nodes,
            "template_hits": hits,
        })
        if ordinal % 25 == 0 or ordinal == len(cases):
            print(f"examined={ordinal}/{len(cases)} hits={counts}", flush=True)

    payload = {
        "format": "krenn-f9-template-coverage-v1",
        "historical_log_sha256": historical_log_sha256,
        "case_inventory_manifest_sha256": case_inventory_manifest_sha256,
        "cases_examined": len(rows),
        "scope": "pending_only" if args.pending_only else "all_historical",
        "templates": [
            {
                "certificate_sha256": template["certificate_sha256"],
                "selected_rows_0based": template["selected"],
                "covered_count": counts[index],
            }
            for index, template in enumerate(templates)
        ],
        "covered_union_count": sum(bool(row["template_hits"]) for row in rows),
        "evaluation_prefilter": {
            "assignment_cycle": evaluation_values,
            "exact_pairs": exact_pairs,
            "incompatible_pairs": incompatible_pairs,
            "rejected_pairs": prefilter_rejected,
        },
        "cases": rows,
    }
    args.output.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n")
    print(json.dumps({
        "covered_union": payload["covered_union_count"],
        "output_sha256": digest(args.output),
        "template_counts": counts,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
