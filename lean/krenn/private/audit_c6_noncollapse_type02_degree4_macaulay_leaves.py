#!/usr/bin/env python3
"""Exact degree-four unit-membership audit for all hard type-2 factor leaves.

The frozen hard `(v0,c2)` localized tail has 369 generators: the complete 360
selected `(3,2,1)` tail, first-stage rows, P-kills, and the theta-inverse
branch relation.  Each of the four domain factor leaves adds two explicit
linear zero generators.

For every leaf this program constructs that exact 371-generator ideal and
tests whether 1 lies in its degree-four Macaulay span over Q.  A generator of
degree d is multiplied by every monomial of degree at most 4-d.  Thus a
positive result would have an explicit finite certificate route.  A negative
result excludes only this bounded-degree unit-certificate family.

The existing `type_02_x0_y0` system is used as a binding regression: its
generator multiset must agree exactly with the constructed first leaf.
"""

from __future__ import annotations

import os
import hashlib
import itertools
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Iterator

from sympy.polys.domains import ZZ
from sympy.polys.matrices import DomainMatrix


ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
PRIVATE = Path(__file__).resolve().parent
if str(PRIVATE) not in sys.path:
    sys.path.insert(0, str(PRIVATE))


FRONTIER = ROOT / "noncollapse_case_artifacts" / "noncollapse_factor_frontier_audit_v1.json"
TAIL_ROOT = ROOT / "noncollapse_case_artifacts" / "generic_slot_tail_v1"
BASE_SYSTEM = TAIL_ROOT / "type_02" / "system.json"
LEAF0_REGRESSION = TAIL_ROOT / "type_02_x0_y0" / "system.json"
TARGET = ROOT / "noncollapse_case_artifacts" / "type02_degree4_macaulay_leaves_v1"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def equation_hash(equation: object) -> str:
    return hashlib.sha256(
        json.dumps(equation, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def weak_compositions(total: int, parts: int, prefix: tuple[int, ...] = ()) -> Iterator[tuple[int, ...]]:
    if parts == 1:
        yield prefix + (total,)
        return
    for value in range(total + 1):
        yield from weak_compositions(total - value, parts - 1, prefix + (value,))


def degree(equation: list[list[object]]) -> int:
    if not equation:
        raise RuntimeError("empty frozen equation")
    return max(sum(exponents) for _coefficient, exponents in equation)


def variable_equation(index: int, variable_count: int) -> list[list[object]]:
    exponents = [0] * variable_count
    exponents[index] = 1
    return [[1, exponents]]


def macauley_rank(equations: list[list[list[object]]], variable_count: int) -> tuple[int, int, int, int]:
    """Return `(rows, touched_monomials, nonzeros, exact_rank)` at degree 4."""
    encoded = [(equation, degree(equation)) for equation in equations]
    monomials: set[tuple[int, ...]] = {(0,) * variable_count}
    rows = 0
    nonzeros = 0
    for equation, polynomial_degree in encoded:
        for multiplier_degree in range(4 - polynomial_degree + 1):
            for multiplier in weak_compositions(multiplier_degree, variable_count):
                rows += 1
                for _coefficient, exponents in equation:
                    monomials.add(tuple(a + b for a, b in zip(exponents, multiplier, strict=True)))
                    nonzeros += 1
    monomial_index = {monomial: index for index, monomial in enumerate(sorted(monomials))}
    sparse_rows: dict[int, dict[int, object]] = {}
    row_index = 0
    for equation, polynomial_degree in encoded:
        for multiplier_degree in range(4 - polynomial_degree + 1):
            for multiplier in weak_compositions(multiplier_degree, variable_count):
                sparse_rows[row_index] = {
                    monomial_index[tuple(a + b for a, b in zip(exponents, multiplier, strict=True))]: ZZ(coefficient)
                    for coefficient, exponents in equation
                }
                row_index += 1
    if row_index != rows:
        raise RuntimeError("Macaulay row inventory drift")
    matrix = DomainMatrix.from_dod(
        sparse_rows, (rows, len(monomial_index)), ZZ
    ).to_field()
    rank = matrix.rank()
    sparse_rows[rows] = {monomial_index[(0,) * variable_count]: ZZ(1)}
    rank_plus_one = DomainMatrix.from_dod(
        sparse_rows, (rows + 1, len(monomial_index)), ZZ
    ).to_field().rank()
    return rows, len(monomial_index), nonzeros, rank, rank_plus_one


def main() -> int:
    frontier = json.loads(FRONTIER.read_text())
    if frontier.get("format") != "krenn-c6-noncollapse-factor-frontier-audit-v1":
        raise RuntimeError("factor-frontier format drift")
    hard = next(row for row in frontier["frontier"] if row["pair_orbit_index"] == 2)
    if hard["factor_branch_count"] != 4:
        raise RuntimeError("hard factor-leaf inventory drift")
    base = json.loads(BASE_SYSTEM.read_text())
    if base.get("format") != "krenn-c6-noncollapse-generic-slot-tail-v1":
        raise RuntimeError("base-tail format drift")
    names = base["variables"]
    base_equations = base["equations"]
    variable_index = {name: index for index, name in enumerate(names)}
    if len(names) != 76 or len(base_equations) != 369 or len(variable_index) != len(names):
        raise RuntimeError("base-tail inventory drift")

    # Bind the constructed first leaf to the previously frozen full leaf.
    existing_leaf0 = json.loads(LEAF0_REGRESSION.read_text())
    leaf0_factor_names = [
        hard["branches"][0]["x_factor"]["symbol"],
        hard["branches"][0]["y_factor"]["symbol"],
    ]
    expected_leaf0 = [*base_equations, *[
        variable_equation(variable_index[name], len(names)) for name in leaf0_factor_names
    ]]
    if Counter(map(equation_hash, expected_leaf0)) != Counter(map(equation_hash, existing_leaf0["equations"])):
        raise RuntimeError("existing leaf-0 system does not bind to parent plus factors")

    TARGET.mkdir(parents=True, exist_ok=True)
    records = []
    members = []
    for leaf_index, branch in enumerate(hard["branches"]):
        factor_names = [branch["x_factor"]["symbol"], branch["y_factor"]["symbol"]]
        if any(name not in variable_index for name in factor_names):
            raise RuntimeError("factor variable absent from base tail")
        equations = [*base_equations, *[
            variable_equation(variable_index[name], len(names)) for name in factor_names
        ]]
        system = {
            "format": "krenn-c6-noncollapse-type02-factor-leaf-degree4-v1",
            "parent_system_file_sha256": sha256(BASE_SYSTEM),
            "parent_system_sha256": base.get("system_sha256"),
            "factor_frontier_sha256": sha256(FRONTIER),
            "factor_leaf_index": leaf_index,
            "factor_zero_generators": factor_names,
            "variables": names,
            "equations": equations,
            "statistics": {
                "variables": len(names),
                "generators": len(equations),
                "degree_histogram": dict(sorted(Counter(map(degree, equations)).items())),
            },
        }
        leaf_dir = TARGET / f"leaf{leaf_index}"
        leaf_dir.mkdir(parents=True, exist_ok=True)
        system_path = leaf_dir / "system.json"
        system_path.write_text(json.dumps(system, indent=2, sort_keys=True) + "\n")
        rows, monomials, nonzeros, rank, rank_plus_one = macauley_rank(equations, len(names))
        member = rank == rank_plus_one
        records.append({
            "leaf_index": leaf_index,
            "system_file_sha256": sha256(system_path),
            "factor_zero_generators": factor_names,
            "degree_bound": 4,
            "macaulay_rows": rows,
            "touched_monomials": monomials,
            "nonzeros": nonzeros,
            "source_span_rank": rank,
            "rank_with_one": rank_plus_one,
            "one_in_degree_four_span": member,
        })
        if member:
            members.append(leaf_index)
        print(f"leaf{leaf_index}: rank={rank}, rank+1={rank_plus_one}, member={member}", flush=True)

    payload = {
        "format": "krenn-c6-noncollapse-type02-degree4-macaulay-leaf-audit-v1",
        "candidate_family": (
            "All degree-at-most-four Macaulay identities for 1 in the full 371-generator "
            "localized hard type-2 factor-leaf ideal."
        ),
        "leaf0_existing_system_multiset_binding": True,
        "records": records,
        "summary": {
            "factor_leaves": len(records),
            "degree_four_unit_members": members,
        },
        "conclusion": {
            "established": (
                "No hard type-2 factor leaf has a unit certificate in the stated degree-four "
                "Macaulay span."
                if not members else
                "At least one leaf has a degree-four unit membership; extract and strictly replay "
                "its coefficient vector before using it."
            ),
            "not_established": (
                "Unit certificates of degree five or greater, non-Macaulay structural proofs, and "
                "all other non-collapse chart types remain outside this audit."
            ),
        },
        "sources": {
            "factor_frontier_sha256": sha256(FRONTIER),
            "base_system_sha256": sha256(BASE_SYSTEM),
            "existing_leaf0_system_sha256": sha256(LEAF0_REGRESSION),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "receipt_payload_sha256": digest(records),
    }
    manifest = TARGET / "manifest.json"
    manifest.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("manifest_sha256=" + sha256(manifest))
    return 2 if members else 0


if __name__ == "__main__":
    raise SystemExit(main())
