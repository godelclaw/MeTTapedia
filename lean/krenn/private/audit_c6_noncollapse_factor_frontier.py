#!/usr/bin/env python3
"""Audit the finite factor frontier left by generic C6 non-collapse charts.

The exact first-stage minor argument is available for seven of the twelve
physical non-collapse pair types.  It gives two cofactor equations ``x = 0``
and ``y = 0``.  Six of those charts have at least one product cofactor, so
over a domain their next honest step is a finite factor split.

This program deliberately answers the question that matters before starting
such a split: do those factor branches *already* enter a previously closed
region?  It checks, exactly and without a CAS search, whether a branch:

* drops the exact C6 mixed support;
* can enter the all-collapse corpus (it cannot while its root theta is
  inverted);
* already supplies a combined P-kill/diagonal-zero doily contradiction; or
* merely exposes additional monomial determinants, which are invitations to
  further kill/collapse reasoning rather than closures.

The output is a finite, source-bound frontier.  It is not a proof that any
unresolved factor branch has a solution, nor a claim that factor splitting is
the best way to close it.
"""

from __future__ import annotations

import os
import hashlib
import itertools
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
import f9_pipeline as pipeline  # noqa: E402
from krenn_exact import perfect_matchings  # noqa: E402


PAIR_AUDIT = ROOT / "noncollapse_case_artifacts" / "noncollapse_pair_chart_audit_v1.json"
TARGET = ROOT / "noncollapse_case_artifacts" / "noncollapse_factor_frontier_audit_v1.json"
SEED_ARTIFACT = (
    ROOT / "noncollapse_case_artifacts" / "slot0_profile321_strict11_v1"
    / "lift_tracked" / "manifest.json"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def parse_weight(name: str) -> tuple[tuple[int, int], int, int] | None:
    match = re.fullmatch(r"w_(\d)(\d)_(\d)(\d)", name)
    if match is None:
        return None
    left, right, source, target = map(int, match.groups())
    return (left, right), source, target


def squarefree_factors(expression: str) -> list[sp.Symbol]:
    _constant, factor_powers = sp.factor_list(sp.sympify(expression))
    answer: list[sp.Symbol] = []
    for factor, power in factor_powers:
        if not isinstance(factor, sp.Symbol):
            raise RuntimeError(f"cofactor unexpectedly has non-variable factor: {factor}")
        answer.extend([factor] * power)
    return answer


PMS = tuple(
    tuple(tuple(sorted(edge)) for edge in matching)
    for matching in perfect_matchings(6)
)


def total_forced_zero(
    dead_p_edges: set[tuple[int, int]],
    diagonal_zero_edges: set[tuple[int, int]],
) -> bool:
    """Exact 15-dimensional doily test for one fixed diagonal colour.

    ``dead_p_edges`` contribute line-sum equations.  A zero diagonal entry
    makes every matching product using that edge zero, so it contributes its
    three coordinate equations.  The total is forced to zero exactly when
    the all-ones row is in their rational row span.
    """
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


def factor_record(symbol: sp.Symbol) -> dict[str, Any]:
    parsed = parse_weight(str(symbol))
    if parsed is None:
        return {"symbol": str(symbol), "kind": "non_weight_symbol"}
    edge, source, target = parsed
    return {
        "symbol": str(symbol),
        "kind": "diagonal" if source == target else "offdiagonal",
        "edge": list(edge),
        "source_colour": source,
        "target_colour": target,
    }


def monomial_determinants(substitution: dict[sp.Symbol, sp.Expr]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for vertex in range(6):
        for colour in range(3):
            determinant = sp.expand(c6.theta_det(vertex, colour).xreplace(substitution))
            if determinant == 0:
                records.append({
                    "slot": {"vertex": vertex, "colour": colour},
                    "kind": "zero",
                })
                continue
            polynomial = sp.Poly(determinant)
            if len(polynomial.terms()) != 1:
                continue
            monomial, coefficient = polynomial.terms()[0]
            factors: list[str] = []
            for variable, exponent in zip(polynomial.gens, monomial, strict=True):
                factors.extend([str(variable)] * exponent)
            records.append({
                "slot": {"vertex": vertex, "colour": colour},
                "kind": "monomial",
                "coefficient": int(coefficient),
                "factors": factors,
            })
    return records


def main() -> int:
    pair_audit = json.loads(PAIR_AUDIT.read_text())
    if pair_audit.get("format") != "krenn-c6-noncollapse-chart-template-audit-v1":
        raise RuntimeError("pair chart audit format drift")
    if pair_audit["summary"] != {
        "affine_or_partially_fixed_types": 5,
        "elevenrow_seed_literal_tail_reproduces": True,
        "generic_four_variable_types": 7,
        "seed_style_first_stage_types": 7,
        "seed_style_literal_tail_closures": 1,
    }:
        raise RuntimeError("pair chart audit summary drift")

    case0 = pipeline.cases_for(c6.X)[0]
    fixed = pipeline.max_fixable([
        (c6.X[index], source, target)
        for index, (source, target) in enumerate(case0)
    ])
    gauge_substitution = {c6.VAR[key]: sp.Integer(1) for key in fixed}
    all_offdiagonal = {
        symbol
        for (edge, source, target), symbol in c6.VAR.items()
        if edge in c6.X and source != target
    }

    generic_types = [
        row for row in pair_audit["types"]
        if row["chart_kind"] == "generic_four_variable"
    ]
    frontier: list[dict[str, Any]] = []
    for row in generic_types:
        type_index = row["pair_orbit_index"]
        representative = row["representative"]
        vertex, colour = representative["vertex"], representative["colour"]
        cofactors = row["first_stage_template"]
        x_factors = squarefree_factors(cofactors["cofactor_x"])
        y_factors = squarefree_factors(cofactors["cofactor_y"])
        branches: list[dict[str, Any]] = []
        for x_factor, y_factor in itertools.product(x_factors, y_factors):
            factors = [x_factor, y_factor]
            factor_data = [factor_record(factor) for factor in factors]
            substitution = {
                **gauge_substitution,
                **{factor: sp.Integer(0) for factor in factors},
            }
            by_colour: dict[int, dict[str, set[tuple[int, int]]]] = {
                c: {"p": set(), "z": set()} for c in range(3)
            }
            for neighbour in c6.NBR[vertex]:
                by_colour[colour]["p"].add(tuple(sorted((vertex, neighbour))))
            factor_set = set(factors)
            for data in factor_data:
                if data["kind"] == "diagonal":
                    by_colour[data["source_colour"]]["z"].add(tuple(data["edge"]))
            doily = []
            for fixed_colour, constraints in by_colour.items():
                p_edges, z_edges = constraints["p"], constraints["z"]
                if not p_edges and not z_edges:
                    continue
                doily.append({
                    "colour": fixed_colour,
                    "dead_p_edges": [list(edge) for edge in sorted(p_edges)],
                    "diagonal_zero_edges": [list(edge) for edge in sorted(z_edges)],
                    "total_forced_zero": total_forced_zero(p_edges, z_edges),
                })
            support_drop_edges = []
            for edge in c6.X:
                channels = {
                    c6.VAR[(edge, source, target)]
                    for source in range(3) for target in range(3)
                    if source != target
                }
                if channels <= factor_set:
                    support_drop_edges.append(list(edge))
            root_theta = sp.expand(c6.theta_det(vertex, colour).xreplace(substitution))
            if root_theta == 0:
                raise RuntimeError(
                    "a factor branch zeroed the inverted root determinant; "
                    "factor/source accounting drift"
                )
            branches.append({
                "x_factor": factor_data[0],
                "y_factor": factor_data[1],
                "support_drop_edges": support_drop_edges,
                "allcollapse_delegation": {
                    "possible": False,
                    "reason": (
                        "The root determinant is explicitly inverted on this "
                        "non-collapse chart and remains nonzero after the two "
                        "factor substitutions."
                    ),
                },
                "doily_constraints_by_colour": doily,
                "immediate_doily_contradiction": any(
                    item["total_forced_zero"] for item in doily
                ),
                "secondary_monomial_determinants": monomial_determinants(substitution),
            })
        frontier.append({
            "pair_orbit_index": type_index,
            "representative": representative,
            "cofactor_x": cofactors["cofactor_x"],
            "cofactor_y": cofactors["cofactor_y"],
            "x_factors": [str(factor) for factor in x_factors],
            "y_factors": [str(factor) for factor in y_factors],
            "factor_branch_count": len(branches),
            "existing_closure": (
                "strict_eleven_row_seed" if type_index == 0 else None
            ),
            "branches": branches,
        })

    branch_count = sum(row["factor_branch_count"] for row in frontier)
    if branch_count != 23:
        raise RuntimeError(f"factor branch census drift: {branch_count}")
    if any(
        branch["support_drop_edges"]
        or branch["immediate_doily_contradiction"]
        for row in frontier for branch in row["branches"]
    ):
        raise RuntimeError(
            "the advertised no-immediate-delegation boundary is false; inspect frontier"
        )
    seed_manifest = json.loads(SEED_ARTIFACT.read_text())
    if seed_manifest.get("verdict") != "strict_exact_identity" or not seed_manifest.get("strict_replay"):
        raise RuntimeError("strict eleven-row seed receipt drift")

    payload = {
        "format": "krenn-c6-noncollapse-factor-frontier-audit-v1",
        "sources": {
            "chart_audit_sha256": sha256(PAIR_AUDIT),
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "f9_pipeline_sha256": sha256(ROOT / "f9_pipeline.py"),
            "audit_script_sha256": sha256(Path(__file__)),
            "seed_manifest_sha256": sha256(SEED_ARTIFACT),
        },
        "gauge_case": [list(item) for item in case0],
        "summary": {
            "generic_chart_types": len(frontier),
            "factor_branches_over_domains": branch_count,
            "branches_closed_by_existing_seed": 1,
            "remaining_factor_branches": branch_count - 1,
            "immediate_support_drops": 0,
            "immediate_allcollapse_delegations": 0,
            "immediate_doily_contradictions": 0,
        },
        "frontier": frontier,
        "conclusion": {
            "established": (
                "Generic non-collapse charts have a finite 23-leaf factor "
                "frontier over a domain, with the seed leaf already strictly "
                "closed.  None of the remaining leaves can honestly be "
                "discarded as an immediate support drop, all-collapse case, "
                "or doily contradiction."
            ),
            "next_obligation": (
                "A new balanced-layer harvest identity must either kill chord "
                "P-lines, close a factor leaf by a small replayable identity, "
                "or supply a justified further finite split.  The listed "
                "secondary monomial determinants are only potential split "
                "sites, not closures."
            ),
        },
    }
    TARGET.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        "C6 NON-COLLAPSE FACTOR FRONTIER VERIFIED: "
        f"{len(frontier)} generic chart types, {branch_count} domain branches, "
        f"{branch_count - 1} unresolved after the known seed"
    )
    print("manifest_sha256=" + sha256(TARGET))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
