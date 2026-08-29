#!/usr/bin/env python3
"""Bounded two-step monomial-determinant strategy audit for C6 non-collapse.

This follows the one-step audit by exactly one additional, logically justified
adjugate dichotomy.  It searches strategies, not solutions: at each state it
may select a theta determinant that has become a monomial after the currently
known factor-zero substitutions.  Its exhaustive children are:

* determinant nonzero, giving the two incident P-line kills;
* determinant zero, split by its variable factors over a domain.

Leaves close only by (i) the exact mixed P-kill/diagonal-zero potential
criterion, or (ii) an explicit conflict with the initially inverted root
determinant.  No Gröbner basis, heuristic algebra, or unrecorded case drop is
used.  The depth bound is deliberately two: a negative result is a reason to
change ideas rather than keep growing this tree without a theorem.
"""

from __future__ import annotations

import os
import hashlib
import json
import re
import sys
from dataclasses import dataclass
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


FRONTIER = ROOT / "noncollapse_case_artifacts" / "noncollapse_factor_frontier_audit_v1.json"
ONE_STEP = ROOT / "noncollapse_case_artifacts" / "noncollapse_secondary_one_step_audit_v1.json"
TARGET = ROOT / "noncollapse_case_artifacts" / "noncollapse_secondary_two_step_audit_v1.json"

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


@dataclass(frozen=True)
class State:
    zero_symbols: tuple[str, ...]
    nonzero_slots: tuple[tuple[int, int], ...]


class Search:
    def __init__(self, representative: dict[str, Any], branch: dict[str, Any], gauge: dict[sp.Symbol, sp.Expr]):
        self.vertex = int(representative["vertex"])
        self.colour = int(representative["colour"])
        self.branch = branch
        self.gauge = gauge
        self.root_slot = (self.vertex, self.colour)
        self.root_theta = c6.theta_det(*self.root_slot)
        self.initial_zero = tuple(sorted({
            branch["x_factor"]["symbol"], branch["y_factor"]["symbol"],
        }))
        self.cache: dict[tuple[State, int], dict[str, Any] | None] = {}
        self.nodes = 0
        self.candidate_nodes = 0
        self.closure_counts = {"potential": 0, "root_conflict": 0}

    def substitution(self, state: State) -> dict[sp.Symbol, sp.Expr]:
        result = dict(self.gauge)
        for name in state.zero_symbols:
            result[sp.Symbol(name)] = sp.Integer(0)
        return result

    def constraints(self, state: State) -> tuple[
        dict[int, set[tuple[int, int]]], dict[int, set[tuple[int, int]]]
    ]:
        p_edges = {colour: set() for colour in range(3)}
        zero_edges = {colour: set() for colour in range(3)}
        for vertex, colour in state.nonzero_slots:
            p_edges[colour].update(
                tuple(sorted((vertex, neighbour))) for neighbour in c6.NBR[vertex]
            )
        for name in state.zero_symbols:
            parsed = parse_weight(name)
            if parsed is None:
                raise RuntimeError(f"unparseable factor {name!r}")
            edge, source, target = parsed
            if source == target:
                zero_edges[source].add(edge)
        return p_edges, zero_edges

    def endpoint_colours(self, state: State) -> list[int]:
        p_edges, zero_edges = self.constraints(state)
        return [
            colour for colour in range(3)
            if forced_total_zero(p_edges[colour], zero_edges[colour])
        ]

    def root_is_forced_zero(self, state: State) -> bool:
        return sp.expand(self.root_theta.xreplace(self.substitution(state))) == 0

    def available(self, state: State) -> list[dict[str, Any]]:
        substitution = self.substitution(state)
        known = set(state.nonzero_slots)
        answer: list[dict[str, Any]] = []
        for vertex in range(6):
            for colour in range(3):
                slot = (vertex, colour)
                if slot in known:
                    continue
                expression = sp.expand(c6.theta_det(vertex, colour).xreplace(substitution))
                if expression == 0:
                    continue
                poly = sp.Poly(expression)
                if len(poly.terms()) != 1:
                    continue
                monomial, coefficient = poly.terms()[0]
                factors: list[str] = []
                for variable, exponent in zip(poly.gens, monomial, strict=True):
                    factors.extend([str(variable)] * exponent)
                answer.append({
                    "slot": slot,
                    "coefficient": str(coefficient),
                    "factors": list(dict.fromkeys(factors)),
                    "expression": str(expression),
                })
        return sorted(answer, key=lambda item: (item["slot"], item["expression"]))

    @staticmethod
    def add_nonzero(state: State, slot: tuple[int, int]) -> State:
        return State(state.zero_symbols, tuple(sorted(set(state.nonzero_slots) | {slot})))

    @staticmethod
    def add_zero(state: State, factor: str) -> State:
        return State(tuple(sorted(set(state.zero_symbols) | {factor})), state.nonzero_slots)

    def terminal(self, state: State) -> dict[str, Any] | None:
        colours = self.endpoint_colours(state)
        if colours:
            self.closure_counts["potential"] += 1
            return {"kind": "potential_endpoint", "colours": colours}
        if self.root_is_forced_zero(state):
            self.closure_counts["root_conflict"] += 1
            return {"kind": "root_nonzero_conflict", "root_slot": self.root_slot}
        return None

    def solve(self, state: State, depth: int) -> dict[str, Any] | None:
        key = (state, depth)
        if key in self.cache:
            return self.cache[key]
        self.nodes += 1
        terminal = self.terminal(state)
        if terminal is not None:
            self.cache[key] = terminal
            return terminal
        if depth == 0:
            self.cache[key] = None
            return None
        for candidate in self.available(state):
            self.candidate_nodes += 1
            slot = tuple(candidate["slot"])
            children: list[tuple[dict[str, Any], State]] = [
                ({"kind": "determinant_nonzero"}, self.add_nonzero(state, slot))
            ]
            children.extend(
                ({"kind": "factor_zero", "factor": factor}, self.add_zero(state, factor))
                for factor in candidate["factors"]
            )
            solved_children: list[dict[str, Any]] = []
            for label, child in children:
                solved = self.solve(child, depth - 1)
                if solved is None:
                    break
                solved_children.append({**label, "result": solved})
            else:
                result = {
                    "kind": "monomial_determinant_strategy",
                    "slot": {"vertex": slot[0], "colour": slot[1]},
                    "expression": candidate["expression"],
                    "factors": candidate["factors"],
                    "children": solved_children,
                }
                self.cache[key] = result
                return result
        self.cache[key] = None
        return None


def main() -> int:
    frontier = json.loads(FRONTIER.read_text())
    one_step = json.loads(ONE_STEP.read_text())
    if frontier.get("summary", {}).get("remaining_factor_branches") != 22:
        raise RuntimeError("factor-frontier branch census drift")
    if one_step.get("summary", {}).get("one_step_all_child_potential_closures") != 0:
        raise RuntimeError("one-step premise drift; inspect before two-step audit")

    case0 = pipeline.cases_for(c6.X)[0]
    fixed = pipeline.max_fixable([
        (c6.X[index], source, target)
        for index, (source, target) in enumerate(case0)
    ])
    gauge = {c6.VAR[key]: sp.Integer(1) for key in fixed}

    records: list[dict[str, Any]] = []
    winning: list[dict[str, Any]] = []
    for family in frontier["frontier"]:
        if family.get("existing_closure"):
            continue
        for branch_index, branch in enumerate(family["branches"]):
            search = Search(family["representative"], branch, gauge)
            initial = State(
                search.initial_zero,
                (search.root_slot,),
            )
            strategy = search.solve(initial, 2)
            record = {
                "pair_orbit_index": family["pair_orbit_index"],
                "factor_branch_index": branch_index,
                "representative": family["representative"],
                "initial_zero_factors": list(initial.zero_symbols),
                "root_slot": {"vertex": search.root_slot[0], "colour": search.root_slot[1]},
                "states_explored": search.nodes,
                "monomial_candidates_examined": search.candidate_nodes,
                "closure_leaf_counts": search.closure_counts,
                "winning_strategy": strategy,
            }
            records.append(record)
            if strategy is not None:
                winning.append(record)

    payload = {
        "format": "krenn-c6-noncollapse-secondary-two-step-audit-v1",
        "sources": {
            "factor_frontier_sha256": sha256(FRONTIER),
            "one_step_audit_sha256": sha256(ONE_STEP),
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "scope": {
            "generic_factor_branches": len(records),
            "depth": 2,
            "branch_rule": (
                "A monomial theta determinant is split only by determinant nonzero "
                "or its exact domain factor-zero alternatives."
            ),
            "closed_leaf_rule": (
                "Only the exact potential endpoint or a forced conflict with the "
                "initially inverted root determinant counts as closed."
            ),
        },
        "summary": {
            "winning_two_step_strategies": len(winning),
            "total_states_explored": sum(record["states_explored"] for record in records),
            "total_monomial_candidates_examined": sum(record["monomial_candidates_examined"] for record in records),
            "potential_terminal_leaves_seen": sum(record["closure_leaf_counts"]["potential"] for record in records),
            "root_conflict_terminal_leaves_seen": sum(record["closure_leaf_counts"]["root_conflict"] for record in records),
        },
        "winning_branches": winning,
        "branches": records,
        "conclusion": {
            "established": (
                "The result is an exact bounded strategy audit of two successive "
                "monomial-determinant dichotomies on the generic factor frontier."
            ),
            "not_established": (
                "A negative outcome does not exclude a theorem using longer balanced "
                "syzygies, affine charts, or a differently motivated finite split."
            ),
        },
    }
    TARGET.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        "C6 SECONDARY TWO-STEP AUDIT: "
        f"{len(records)} factor branches; {len(winning)} winning strategies; "
        f"{payload['summary']['total_states_explored']} states"
    )
    print("manifest_sha256=" + sha256(TARGET))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
