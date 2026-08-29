#!/usr/bin/env python3
"""Build and query a sound Boolean shadow of the frozen chart-0 system.

For a polynomial over an integral domain, a monomial is nonzero exactly when
all variables occurring in it are nonzero.  Consequently a polynomial that is
equal to zero cannot have exactly one nonzero monomial.  This script encodes
only that necessary condition, then adds exact support assignments excluded by
strictly replayed factor-branch certificates.

UNSAT is therefore a sound contradiction for the frozen algebraic system.
SAT only says that this deliberately incomplete support abstraction has not
decided the algebraic problem.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Any, NoReturn

from pysat.solvers import Solver


AUDIT_FORMAT = "krenn-chart0-factor-inverse-baseline-audit-v1"
INVENTORY_FORMAT = "krenn-frozen-coordinate-branch-inventory-v1"
OUTPUT_FORMAT = "krenn-chart0-support-theory-v1"


def fail(message: str) -> NoReturn:
    raise SystemExit("CHART0 SUPPORT THEORY FAILED: " + message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        fail(f"cannot read {path}: {error}")


def write_dimacs(path: Path, variable_count: int, clauses: list[list[int]],
                 variable_names: list[str]) -> None:
    # Mathlib's deliberately small DIMACS parser rejects comment lines.  The
    # support-variable map is stored in the hashed JSON manifest instead.
    lines = [f"p cnf {variable_count} {len(clauses)}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    path.write_text("\n".join(lines) + "\n", encoding="ascii")


def canonical_equation(raw: Any, variable_count: int, equation_index: int) \
        -> list[tuple[Fraction, tuple[int, ...]]]:
    if not isinstance(raw, list):
        fail(f"equation {equation_index} is not a list")
    combined: dict[tuple[int, ...], Fraction] = {}
    for term_index, term in enumerate(raw):
        if not isinstance(term, list) or len(term) != 2:
            fail(f"equation {equation_index} term {term_index} is malformed")
        coefficient, exponents = term
        if type(coefficient) is not int:
            fail(f"equation {equation_index} term {term_index} coefficient is not an integer")
        if not isinstance(exponents, list) or len(exponents) != variable_count:
            fail(f"equation {equation_index} term {term_index} exponent-vector length mismatch")
        if any(type(exponent) is not int or exponent < 0 for exponent in exponents):
            fail(f"equation {equation_index} term {term_index} has an invalid exponent")
        key = tuple(exponents)
        combined[key] = combined.get(key, Fraction(0)) + Fraction(coefficient)
    return sorted(
        [(coefficient, exponents) for exponents, coefficient in combined.items() if coefficient],
        key=lambda item: item[1],
    )


def add_equation_support_clauses(
    clauses: list[list[int]],
    equation: list[tuple[Fraction, tuple[int, ...]]],
    next_variable: int,
) -> tuple[int, int]:
    """Return the next unused variable and number of monomial auxiliaries."""
    monomial_variables: list[int] = []
    for _, exponents in equation:
        auxiliary = next_variable
        next_variable += 1
        monomial_variables.append(auxiliary)
        factors = [index + 1 for index, exponent in enumerate(exponents) if exponent]
        if not factors:
            clauses.append([auxiliary])
            continue
        # auxiliary <-> conjunction(factors)
        clauses.extend([[-auxiliary, factor] for factor in factors])
        clauses.append([auxiliary] + [-factor for factor in factors])

    # A zero polynomial cannot have exactly one nonzero monomial.
    if len(monomial_variables) == 1:
        clauses.append([-monomial_variables[0]])
    elif len(monomial_variables) >= 2:
        for index, monomial in enumerate(monomial_variables):
            clauses.append([-monomial] + monomial_variables[:index] + monomial_variables[index + 1 :])
    return next_variable, len(monomial_variables)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("audit", type=Path)
    parser.add_argument("probe_root", type=Path)
    parser.add_argument("strict_checker", type=Path)
    parser.add_argument("output_prefix", type=Path)
    parser.add_argument("--query-zero", required=True)
    parser.add_argument("--drat-trim", type=Path, required=True)
    parser.add_argument("--lrat-check", type=Path, required=True)
    args = parser.parse_args()

    system = load_json(args.system)
    audit = load_json(args.audit)
    system_file_sha256 = sha256(args.system)
    if audit.get("format") != AUDIT_FORMAT:
        fail("unexpected factor-audit format")
    if audit.get("system_file_sha256") != system_file_sha256:
        fail("factor audit is not bound to the frozen parent bytes")

    variables = system.get("variables")
    equations = system.get("equations")
    if not isinstance(variables, list) or len(set(variables)) != len(variables):
        fail("frozen system has malformed or duplicate variable names")
    if not all(isinstance(name, str) and name for name in variables):
        fail("frozen system has an invalid variable name")
    if not isinstance(equations, list):
        fail("frozen system has no equation list")
    variable_id = {name: index + 1 for index, name in enumerate(variables)}
    if args.query_zero not in variable_id:
        fail(f"query variable {args.query_zero!r} is absent")

    # Import the authoritative strict checker from the exact requested file.
    sys.path.insert(0, str(args.strict_checker.parent))
    try:
        from strict_certificate_checker import CertificateError, check_c4  # type: ignore
    except ImportError as error:
        fail(f"cannot import strict checker: {error}")
    if Path(sys.modules["strict_certificate_checker"].__file__).resolve() != args.strict_checker.resolve():
        fail("imported strict checker does not match the requested path")

    clauses: list[list[int]] = []
    clause_kinds: Counter[str] = Counter()
    next_variable = len(variables) + 1
    monomial_count = 0
    for equation_index, raw_equation in enumerate(equations):
        equation = canonical_equation(raw_equation, len(variables), equation_index)
        before = len(clauses)
        next_variable, added_monomials = add_equation_support_clauses(
            clauses, equation, next_variable
        )
        monomial_count += added_monomials
        clause_kinds["polynomial_support"] += len(clauses) - before

    for coordinate in system.get("zero_coordinates", []):
        if coordinate not in variable_id:
            fail(f"declared zero coordinate {coordinate!r} is absent")
        clauses.append([-variable_id[coordinate]])
        clause_kinds["declared_zero"] += 1
    for coordinate in system.get("nonzero_coordinates", []):
        if coordinate not in variable_id:
            fail(f"declared nonzero coordinate {coordinate!r} is absent")
        clauses.append([variable_id[coordinate]])
        clause_kinds["declared_nonzero"] += 1

    strict_sources: list[dict[str, Any]] = []
    rows = audit.get("rows")
    if not isinstance(rows, list):
        fail("factor audit has no row list")
    for row in rows:
        equation_index = row.get("equation")
        coordinates = row.get("coordinates")
        closures = row.get("nontrivial_closures")
        if type(equation_index) is not int or not isinstance(coordinates, list) \
                or not isinstance(closures, list):
            fail("malformed factor-audit row")
        if any(coordinate not in variable_id for coordinate in coordinates):
            fail(f"row {equation_index} references an absent coordinate")
        row_root = args.probe_root / f"row{equation_index}_split"
        inventory_path = row_root / "inventory.json"
        inventory = load_json(inventory_path)
        if inventory.get("format") != INVENTORY_FORMAT:
            fail(f"row {equation_index}: unexpected inventory format")
        if inventory.get("source_system_file_sha256") != system_file_sha256:
            fail(f"row {equation_index}: inventory parent hash mismatch")
        if inventory.get("coordinates") != coordinates:
            fail(f"row {equation_index}: inventory coordinate mismatch")
        inventory_branches = inventory.get("branches")
        if not isinstance(inventory_branches, list):
            fail(f"row {equation_index}: inventory has no branch list")
        by_index = {branch.get("branch"): branch for branch in inventory_branches}

        for branch_index in closures:
            if type(branch_index) is not int or branch_index not in by_index:
                fail(f"row {equation_index}: invalid closure branch {branch_index!r}")
            branch = by_index[branch_index]
            bits = branch.get("nonzero_bits")
            if not isinstance(bits, list) or len(bits) != len(coordinates) \
                    or any(bit not in (0, 1) for bit in bits):
                fail(f"row {equation_index} branch {branch_index}: malformed bits")
            branch_root = row_root / f"branch_{branch_index}"
            branch_system = branch_root / "system.json"
            certificate = branch_root / "lift.stdout"
            branch_system_sha256 = sha256(branch_system)
            if branch_system_sha256 != branch.get("system_file_sha256"):
                fail(f"row {equation_index} branch {branch_index}: system hash mismatch")
            try:
                replay = check_c4(branch_system, certificate)
            except (CertificateError, OSError, json.JSONDecodeError) as error:
                fail(f"row {equation_index} branch {branch_index}: strict replay failed: {error}")
            if replay.get("system_file_sha256") != branch_system_sha256:
                fail(f"row {equation_index} branch {branch_index}: replay binding mismatch")

            # Exclude this exact support assignment.
            clauses.append([
                -variable_id[coordinate] if bit else variable_id[coordinate]
                for coordinate, bit in zip(coordinates, bits, strict=True)
            ])
            clause_kinds["strict_factor_no_good"] += 1
            strict_sources.append({
                "equation": equation_index,
                "branch": branch_index,
                "coordinates": coordinates,
                "nonzero_bits": bits,
                "branch_system_file_sha256": branch_system_sha256,
                "certificate_file_sha256": replay["certificate_file_sha256"],
                "nonzero_multiplier_indices_1based": replay["nonzero_multiplier_indices_1based"],
            })

    base_variable_count = next_variable - 1
    base_cnf = args.output_prefix.with_suffix(".cnf")
    query_cnf = args.output_prefix.with_name(args.output_prefix.name + "_query_zero").with_suffix(".cnf")
    query_drat = args.output_prefix.with_name(args.output_prefix.name + "_query_zero").with_suffix(".drat")
    query_lrat = args.output_prefix.with_name(args.output_prefix.name + "_query_zero").with_suffix(".lrat")
    output_json = args.output_prefix.with_suffix(".json")
    args.output_prefix.parent.mkdir(parents=True, exist_ok=True)
    write_dimacs(base_cnf, base_variable_count, clauses, variables)

    query_literal = -variable_id[args.query_zero]
    query_clauses = clauses + [[query_literal]]
    write_dimacs(query_cnf, base_variable_count, query_clauses, variables)

    with Solver(name="cadical195", bootstrap_with=clauses) as solver:
        base_sat = solver.solve()
        if not base_sat:
            fail("base support theory is inconsistent before the requested query")
        query_sat = solver.solve(assumptions=[query_literal])
        query_model: dict[str, bool] | None = None
        backbones: dict[str, bool] = {}
        if query_sat:
            raw_model = set(solver.get_model())
            query_model = {name: identifier in raw_model for name, identifier in variable_id.items()}
            for name, identifier in variable_id.items():
                value = query_model[name]
                opposite = -identifier if value else identifier
                if not solver.solve(assumptions=[query_literal, opposite]):
                    backbones[name] = value

    query_drat_sha256: str | None = None
    if not query_sat:
        # Solve the materialized query CNF, rather than relying on an assumption
        # proof whose implicit unit would not be present during independent replay.
        with Solver(name="glucose4", bootstrap_with=query_clauses, with_proof=True) as solver:
            if solver.solve():
                fail("materialized query unexpectedly differs from the assumption query")
            proof = solver.get_proof()
        if not proof or proof[-1].strip() != "0":
            fail("CaDiCaL returned no terminating DRAT refutation")
        query_drat.write_text("\n".join(proof) + "\n", encoding="ascii")
        query_drat_sha256 = sha256(query_drat)
        try:
            conversion = subprocess.run(
                [str(args.drat_trim), str(query_cnf), str(query_drat), "-L", str(query_lrat)],
                check=True,
                capture_output=True,
                text=True,
            )
            replay = subprocess.run(
                [str(args.lrat_check), str(query_cnf), str(query_lrat)],
                check=True,
                capture_output=True,
                text=True,
            )
        except (OSError, subprocess.CalledProcessError) as error:
            fail(f"DRAT conversion or LRAT replay failed: {error}")
        if "s VERIFIED" not in conversion.stdout or "c VERIFIED" not in replay.stdout:
            fail("external DRAT/LRAT tools did not report VERIFIED")

    result = {
        "format": OUTPUT_FORMAT,
        "inputs": {
            "system_file_sha256": system_file_sha256,
            "factor_audit_file_sha256": sha256(args.audit),
            "strict_checker_file_sha256": sha256(args.strict_checker),
        },
        "encoding": {
            "support_variables": len(variables),
            "support_variable_names": variables,
            "monomial_auxiliaries": monomial_count,
            "cnf_variables": base_variable_count,
            "base_clauses": len(clauses),
            "query_clauses": len(query_clauses),
            "clause_kinds": dict(sorted(clause_kinds.items())),
            "base_cnf_sha256": sha256(base_cnf),
            "query_cnf_sha256": sha256(query_cnf),
            "query_drat_sha256": query_drat_sha256,
            "query_lrat_sha256": sha256(query_lrat) if not query_sat else None,
        },
        "strict_factor_sources": strict_sources,
        "proof_tools": {
            "drat_trim_file_sha256": sha256(args.drat_trim),
            "lrat_check_file_sha256": sha256(args.lrat_check),
        },
        "query": {"coordinate": args.query_zero, "nonzero": False},
        "base_satisfiable": base_sat,
        "query_satisfiable": query_sat,
        "query_model": query_model,
        "query_backbones": backbones,
        "interpretation": (
            "UNSAT is a sound algebraic contradiction; SAT only means the necessary support abstraction is insufficient."
        ),
    }
    output_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "output": str(output_json),
        "base_satisfiable": base_sat,
        "query_satisfiable": query_sat,
        "query_backbones": backbones,
        "strict_factor_no_goods": len(strict_sources),
        "cnf_variables": base_variable_count,
        "base_clauses": len(clauses),
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
