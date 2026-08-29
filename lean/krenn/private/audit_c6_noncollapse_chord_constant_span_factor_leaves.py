#!/usr/bin/env python3
"""Exact constant-span test for the required non-collapse chord P-kills.

This is the first widening after the one/two-row audit.  On each of the four
domain factor leaves of the hard generic non-collapse chart, it asks whether
any P-line needed by a *minimal* doily completion lies in the full rational
constant-coefficient span of all 729 normalized frozen amplitude rows,
modulo the two already-known incident P-kills and the two leaf factors.

The computation is finite linear algebra over Q, not a Gröbner search.  A
positive entry is intentionally not called a certificate here: it must be
extracted into a framed identity and strictly replayed before being used.  A
negative entry is an exact exclusion of this constant-multiplier family only.
"""

from __future__ import annotations

import os
import hashlib
import itertools
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any

import sympy as sp
from sympy.polys.domains import ZZ
from sympy.polys.matrices import DomainMatrix


ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
PRIVATE = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(PRIVATE) not in sys.path:
    sys.path.insert(0, str(PRIVATE))

import c6_collapse_attack as c6  # noqa: E402
import f9_pipeline as pipeline  # noqa: E402
from audit_c6_noncollapse_factor_frontier import total_forced_zero  # noqa: E402


FRONTIER = ROOT / "noncollapse_case_artifacts" / "noncollapse_factor_frontier_audit_v1.json"
LOW_SUPPORT = ROOT / "noncollapse_case_artifacts" / "noncollapse_chord_low_support_factor_leaf_audit_v1.json"
TARGET = ROOT / "noncollapse_case_artifacts" / "noncollapse_chord_constant_span_factor_leaf_audit_v1.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def profile(colours: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(Counter(colours).values(), reverse=True))


def terms(expression: sp.Expr, variables: list[sp.Symbol]) -> list[tuple[tuple[int, ...], int]]:
    return [
        (powers, int(coefficient))
        for powers, coefficient in sp.Poly(expression, *variables, domain=sp.ZZ).terms()
        if coefficient
    ]


def factor_symbol(record: dict[str, Any]) -> sp.Symbol:
    if record.get("kind") not in {"diagonal", "offdiagonal"}:
        raise RuntimeError("factor frontier supplied a non-weight factor")
    return sp.Symbol(record["symbol"])


def minimal_completions(
    base: set[tuple[int, int]], zeros: set[tuple[int, int]]
) -> list[tuple[tuple[int, int], ...]]:
    all_edges = [(a, b) for a in range(6) for b in range(a + 1, 6)]
    available = [edge for edge in all_edges if edge not in base]
    for size in range(1, len(available) + 1):
        hits = [
            candidate for candidate in itertools.combinations(available, size)
            if total_forced_zero(base | set(candidate), zeros)
        ]
        if hits:
            return hits
    raise RuntimeError("all P-lines should force a doily contradiction")


def rank_of(rows: list[list[tuple[tuple[int, ...], int]]], monomial_index: dict[tuple[int, ...], int]) -> int:
    matrix = DomainMatrix.from_dod(
        {
            row: {monomial_index[monomial]: ZZ(coefficient)
                  for monomial, coefficient in terms_row}
            for row, terms_row in enumerate(rows)
        },
        (len(rows), len(monomial_index)),
        ZZ,
    ).to_field()
    return matrix.rank()


def main() -> int:
    frontier = json.loads(FRONTIER.read_text())
    if frontier.get("format") != "krenn-c6-noncollapse-factor-frontier-audit-v1":
        raise RuntimeError("factor-frontier format drift")
    low_support = json.loads(LOW_SUPPORT.read_text())
    if low_support.get("format") != "krenn-c6-noncollapse-chord-low-support-factor-leaf-audit-v1":
        raise RuntimeError("low-support audit format drift")
    if low_support["summary"] != {
        "factor_leaves": 4,
        "low_support_p_kill_matches": 0,
        "minimal_completion_size": 3,
    }:
        raise RuntimeError("low-support audit result drift")
    hard = next(row for row in frontier["frontier"] if row["pair_orbit_index"] == 2)

    vertex, colour = 0, 2
    left, right = c6.NBR[vertex]
    case0 = pipeline.cases_for(c6.X)[0]
    fixed = pipeline.max_fixable([
        (c6.X[index], source, target)
        for index, (source, target) in enumerate(case0)
    ])
    substitution = {c6.VAR[key]: sp.Integer(1) for key in fixed}
    p_left = sp.expand(c6.P(vertex, left, colour).xreplace(substitution))
    p_right = sp.expand(c6.P(vertex, right, colour).xreplace(substitution))

    source_rows: list[dict[str, Any]] = []
    for colours in itertools.product(range(3), repeat=6):
        kind = profile(colours)
        equation = sp.expand(
            c6.pm_sum(dict(enumerate(colours))).xreplace(substitution)
            - (1 if kind == (6,) else 0)
        )
        if equation != 0:
            source_rows.append({"profile": list(kind), "equation": equation})
    if len(source_rows) != 729:
        raise RuntimeError("frozen C6 row census drift")
    variables = sorted(
        {symbol for row in source_rows for symbol in row["equation"].free_symbols}
        | p_left.free_symbols | p_right.free_symbols,
        key=sp.default_sort_key,
    )

    leaf_records = []
    positive = []
    for branch_index, branch in enumerate(hard["branches"]):
        doily = branch["doily_constraints_by_colour"]
        if len(doily) != 1 or doily[0]["colour"] != colour:
            raise RuntimeError("hard leaf doily data drift")
        base = {tuple(edge) for edge in doily[0]["dead_p_edges"]}
        zeros = {tuple(edge) for edge in doily[0]["diagonal_zero_edges"]}
        completions = minimal_completions(base, zeros)
        factors = [factor_symbol(branch["x_factor"]), factor_symbol(branch["y_factor"])]
        groebner = sp.groebner([p_left, p_right, *factors], *variables, order="lex")
        reduced = []
        for row in source_rows:
            quotients, remainder = groebner.reduce(row["equation"])
            replay = sp.expand(
                row["equation"] - remainder
                - sum(quotient * basis.as_expr()
                      for quotient, basis in zip(quotients, groebner.polys, strict=True)))
            if replay != 0:
                raise RuntimeError("leaf reduction replay drift")
            reduced.append(terms(remainder, variables))
        target_edges = sorted({edge for completion in completions for edge in completion})
        target_terms: dict[tuple[int, int], list[tuple[tuple[int, ...], int]]] = {
            edge: terms(sp.expand(c6.P(edge[0], edge[1], colour).xreplace(substitution)), variables)
            for edge in target_edges
        }
        all_monomials = {
            monomial for row in reduced for monomial, _coefficient in row
        } | {
            monomial for row in target_terms.values() for monomial, _coefficient in row
        }
        monomial_index = {monomial: index for index, monomial in enumerate(sorted(all_monomials))}
        span_rank = rank_of(reduced, monomial_index)
        target_records = []
        for edge in target_edges:
            target_row = target_terms[edge]
            if not target_row:
                target_records.append({
                    "edge": list(edge),
                    "target_is_zero_mod_leaf_constraints": True,
                    "span_member": True,
                    "rank_with_target": span_rank,
                })
                positive.append({"branch_index": branch_index, "edge": list(edge), "kind": "zero_mod_constraints"})
                continue
            rank_with_target = rank_of([*reduced, target_row], monomial_index)
            member = rank_with_target == span_rank
            target_records.append({
                "edge": list(edge),
                "target_is_zero_mod_leaf_constraints": False,
                "span_member": member,
                "rank_with_target": rank_with_target,
            })
            if member:
                positive.append({"branch_index": branch_index, "edge": list(edge), "kind": "constant_span"})
        leaf_records.append({
            "branch_index": branch_index,
            "factor_zero_generators": [str(factor) for factor in factors],
            "minimal_doily_completion_size": len(completions[0]),
            "minimal_doily_completions": [[list(edge) for edge in completion] for completion in completions],
            "ambient_monomials": len(monomial_index),
            "source_rows": len(reduced),
            "source_constant_span_rank": span_rank,
            "targets": target_records,
        })

    payload = {
        "format": "krenn-c6-noncollapse-chord-constant-span-factor-leaf-audit-v1",
        "scope": {
            "pair_orbit_index": 2,
            "slot": {"vertex": vertex, "colour": colour, "neighbours": [left, right]},
            "known_p_kills": [str(p_left), str(p_right)],
            "source_rows": len(source_rows),
        },
        "candidate_family": (
            "The full rational constant-coefficient span of all 729 normalized frozen "
            "amplitude rows, reduced exactly modulo the two slot P-kills and one hard "
            "factor leaf, contains a P-line from a minimal doily completion."
        ),
        "factor_leaves": leaf_records,
        "summary": {
            "factor_leaves": len(leaf_records),
            "constant_span_p_kill_matches": len(positive),
            "minimal_completion_size": 3,
        },
        "conclusion": {
            "established": (
                "No required chord P-kill belongs to the stated exact constant-coefficient "
                "row span on any hard factor leaf."
                if not positive else
                "At least one required P-kill lies in the constant row span; extract and "
                "strictly replay its coefficient vector before using it."
            ),
            "not_established": (
                "Polynomial-multiplier syzygies, three-or-more-row identities with nonconstant "
                "coefficients, and other non-collapse chart types remain outside this audit."
            ),
        },
        "sources": {
            "factor_frontier_sha256": sha256(FRONTIER),
            "low_support_audit_sha256": sha256(LOW_SUPPORT),
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "f9_pipeline_sha256": sha256(ROOT / "f9_pipeline.py"),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "receipt_payload_sha256": digest({
            "factor_leaves": leaf_records,
            "positive": positive,
        }),
    }
    TARGET.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    if positive:
        print("C6 CONSTANT-SPAN FACTOR-LEAF AUDIT FOUND MEMBERS: " + str(len(positive)))
        return 2
    print(
        "C6 CONSTANT-SPAN FACTOR-LEAF AUDIT VERIFIED: "
        f"{len(leaf_records)} leaves, no required chord P-kill in row spans"
    )
    print("manifest_sha256=" + sha256(TARGET))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
