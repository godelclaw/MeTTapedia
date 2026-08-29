#!/usr/bin/env python3
"""One exact secondary-determinant closure test for C6 non-collapse leaves.

The factor-frontier audit leaves 22 generic non-collapse factor branches.
Some branches make other adjugate determinants monomials.  For one such
determinant ``D = c * f₁ * ... * fₖ``, a domain witness has an exhaustive,
small dichotomy:

* ``D != 0``: the two adjugate identities kill the two P-lines incident to
  the determinant's slot;
* ``D = 0``: one of the displayed factors is zero.

This program asks the narrow, useful question whether *every* child of one
such dichotomy already reaches the independently checked doily endpoint.
It accepts both kinds of line death: a P-line kill and a diagonal edge zero
(the latter kills all matching products through that edge).

It is a combinatorial eligibility audit, not a claim that a positive result
has yet been reflected through the frozen source equations.  A positive
candidate would identify a short, formally provable next lemma; a negative
result cleanly rules out this one-step route.
"""

from __future__ import annotations

import os
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

import sympy as sp


ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
PRIVATE = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import c6_collapse_attack as c6  # noqa: E402
from krenn_exact import perfect_matchings  # noqa: E402


FRONTIER = ROOT / "noncollapse_case_artifacts" / "noncollapse_factor_frontier_audit_v1.json"
TARGET = ROOT / "noncollapse_case_artifacts" / "noncollapse_secondary_one_step_audit_v1.json"

PMS = tuple(
    tuple(tuple(sorted(edge)) for edge in matching)
    for matching in perfect_matchings(6)
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_weight(name: str) -> tuple[tuple[int, int], int, int] | None:
    match = re.fullmatch(r"w_(\d)(\d)_(\d)(\d)", name)
    if match is None:
        return None
    left, right, source, target = map(int, match.groups())
    return (left, right), source, target


def forced_total_zero(
    dead_p_edges: set[tuple[int, int]],
    diagonal_zero_edges: set[tuple[int, int]],
) -> bool:
    """Exact line-sum/diagonal-zero test for one monochromatic slice."""
    rows: list[list[int]] = []
    for edge in sorted(dead_p_edges):
        rows.append([int(edge in matching) for matching in PMS])
    for edge in sorted(diagonal_zero_edges):
        for index, matching in enumerate(PMS):
            if edge in matching:
                row = [0] * len(PMS)
                row[index] = 1
                rows.append(row)
    if not rows:
        return False
    constraints = sp.Matrix(rows)
    total = sp.Matrix([[1] * len(PMS)])
    return constraints.rank() == constraints.col_join(total).rank()


def initial_constraints(branch: dict[str, Any], representative: dict[str, Any]) -> tuple[
    dict[int, set[tuple[int, int]]], dict[int, set[tuple[int, int]]]
]:
    p_edges = {colour: set() for colour in range(3)}
    zero_edges = {colour: set() for colour in range(3)}
    vertex = int(representative["vertex"])
    colour = int(representative["colour"])
    p_edges[colour].update(tuple(sorted((vertex, neighbour))) for neighbour in c6.NBR[vertex])
    for factor_key in ("x_factor", "y_factor"):
        factor = branch[factor_key]
        if factor["kind"] == "diagonal":
            zero_edges[int(factor["source_colour"])].add(tuple(factor["edge"]))
    return p_edges, zero_edges


def add_diagonal_factor(
    zero_edges: dict[int, set[tuple[int, int]]], factor: str,
) -> None:
    parsed = parse_weight(factor)
    if parsed is None:
        raise RuntimeError(f"unparseable monomial factor {factor!r}")
    edge, source, target = parsed
    if source == target:
        zero_edges[source].add(edge)


def endpoint_colours(
    p_edges: dict[int, set[tuple[int, int]]],
    zero_edges: dict[int, set[tuple[int, int]]],
) -> list[int]:
    return [
        colour for colour in range(3)
        if forced_total_zero(p_edges[colour], zero_edges[colour])
    ]


def child_record(
    kind: str,
    factor: str | None,
    slot: dict[str, int],
    base_p: dict[int, set[tuple[int, int]]],
    base_zero: dict[int, set[tuple[int, int]]],
) -> dict[str, Any]:
    p_edges = {colour: set(edges) for colour, edges in base_p.items()}
    zero_edges = {colour: set(edges) for colour, edges in base_zero.items()}
    if kind == "determinant_nonzero":
        vertex, colour = int(slot["vertex"]), int(slot["colour"])
        p_edges[colour].update(tuple(sorted((vertex, neighbor))) for neighbor in c6.NBR[vertex])
    elif kind == "factor_zero":
        assert factor is not None
        add_diagonal_factor(zero_edges, factor)
    else:
        raise RuntimeError(f"unknown child kind {kind}")
    closes = endpoint_colours(p_edges, zero_edges)
    return {
        "kind": kind,
        "factor": factor,
        "endpoint_colours": closes,
        "potential_endpoint": bool(closes),
        "p_edges": {str(c): [list(edge) for edge in sorted(edges)] for c, edges in p_edges.items() if edges},
        "diagonal_zero_edges": {
            str(c): [list(edge) for edge in sorted(edges)]
            for c, edges in zero_edges.items() if edges
        },
    }


def main() -> int:
    frontier = json.loads(FRONTIER.read_text())
    if frontier.get("format") != "krenn-c6-noncollapse-factor-frontier-audit-v1":
        raise RuntimeError("factor-frontier format drift")
    if frontier.get("summary", {}).get("remaining_factor_branches") != 22:
        raise RuntimeError("factor-frontier branch census drift")

    records: list[dict[str, Any]] = []
    unresolved_branches = 0
    for family in frontier["frontier"]:
        if family.get("existing_closure"):
            continue
        representative = family["representative"]
        for branch_index, branch in enumerate(family["branches"]):
            unresolved_branches += 1
            base_p, base_zero = initial_constraints(branch, representative)
            monomials = [
                determinant for determinant in branch["secondary_monomial_determinants"]
                if determinant["kind"] == "monomial"
            ]
            for determinant in monomials:
                factors = list(dict.fromkeys(determinant["factors"]))
                children = [
                    child_record("determinant_nonzero", None, determinant["slot"], base_p, base_zero)
                ]
                children.extend(
                    child_record("factor_zero", factor, determinant["slot"], base_p, base_zero)
                    for factor in factors
                )
                records.append({
                    "pair_orbit_index": family["pair_orbit_index"],
                    "factor_branch_index": branch_index,
                    "representative": representative,
                    "secondary_slot": determinant["slot"],
                    "coefficient": determinant["coefficient"],
                    "factors": factors,
                    "all_children_reach_potential_endpoint": all(
                        child["potential_endpoint"] for child in children
                    ),
                    "children": children,
                })

    closing = [record for record in records if record["all_children_reach_potential_endpoint"]]
    payload = {
        "format": "krenn-c6-noncollapse-secondary-one-step-audit-v1",
        "sources": {
            "factor_frontier_sha256": sha256(FRONTIER),
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "scope": {
            "unresolved_generic_factor_branches": unresolved_branches,
            "rule": (
                "For one secondary monomial determinant, split into its nonzero "
                "adjugate-P-kill child and its domain-justified zero-factor children."
            ),
            "endpoint": (
                "The exact K6 line-sum potential criterion, allowing both P-line "
                "kills and diagonal-zero line kills."
            ),
        },
        "summary": {
            "secondary_monomial_candidates": len(records),
            "one_step_all_child_potential_closures": len(closing),
            "branches_with_a_one_step_closure": len({
                (record["pair_orbit_index"], record["factor_branch_index"])
                for record in closing
            }),
        },
        "closing_candidates": closing,
        "candidates": records,
        "conclusion": {
            "established": (
                "This audit records exactly which one-secondary-determinant "
                "dichotomies reach the existing potential endpoint in every child."
            ),
            "not_established": (
                "A negative result does not rule out two-step determinant splits, "
                "longer balanced syzygies, or affine non-collapse chart arguments."
            ),
        },
    }
    TARGET.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        "C6 SECONDARY ONE-STEP AUDIT: "
        f"{len(records)} monomial candidates across {unresolved_branches} branches; "
        f"{len(closing)} all-child potential closures"
    )
    print("manifest_sha256=" + sha256(TARGET))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
