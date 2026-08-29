#!/usr/bin/env python3
"""Test the smallest possible chord-P harvest identity in one hard C6 chart.

For the generic non-collapse representative `(vertex 0, colour 2)`, let
``a,b,c,d`` be the entries of its inverted theta minor and let ``Q`` be a
chord-side diagonal co-sum.  The most economical way to obtain
``theta * Q`` from two balanced equations would be an adjugate pair:

``R₁ = s*a*Q + b*X,   R₂ = s*c*Q + d*X``

or its column-swapped analogue.  Then `d*R₁ - b*R₂ = s*theta*Q`.

This audit exhausts that sharply delimited two-row template after exact
reduction by the two P-kills already supplied by the non-collapse slot.  It
is a negative design result if no pair appears: it does *not* rule out a
longer syzygy, a product-factor argument, or a different balanced profile.
"""

from __future__ import annotations

import os
import hashlib
import itertools
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

import sympy as sp


ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import c6_collapse_attack as c6  # noqa: E402
import f9_pipeline as pipeline  # noqa: E402


TARGET = ROOT / "noncollapse_case_artifacts" / "noncollapse_chord_adjugate_pair_audit_v1.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def profile(colours: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(Counter(colours).values(), reverse=True))


def sparse(expression: sp.Expr, variables: list[sp.Symbol]) -> dict[tuple[int, ...], int]:
    polynomial = sp.Poly(expression, *variables, domain=sp.ZZ)
    return {powers: int(coefficient) for powers, coefficient in polynomial.terms()}


def multiply_by_variable(
    polynomial: dict[tuple[int, ...], int], index: int
) -> dict[tuple[int, ...], int]:
    answer: dict[tuple[int, ...], int] = {}
    for powers, coefficient in polynomial.items():
        updated = list(powers)
        updated[index] += 1
        key = tuple(updated)
        answer[key] = answer.get(key, 0) + coefficient
    return {powers: coefficient for powers, coefficient in answer.items() if coefficient}


def subtract(
    left: dict[tuple[int, ...], int], right: dict[tuple[int, ...], int]
) -> dict[tuple[int, ...], int]:
    answer = dict(left)
    for powers, coefficient in right.items():
        answer[powers] = answer.get(powers, 0) - coefficient
        if not answer[powers]:
            del answer[powers]
    return answer


def negate(polynomial: dict[tuple[int, ...], int]) -> dict[tuple[int, ...], int]:
    return {powers: -coefficient for powers, coefficient in polynomial.items()}


def divide_by_variable(
    polynomial: dict[tuple[int, ...], int], index: int
) -> dict[tuple[int, ...], int] | None:
    answer: dict[tuple[int, ...], int] = {}
    for powers, coefficient in polynomial.items():
        if powers[index] == 0:
            return None
        updated = list(powers)
        updated[index] -= 1
        answer[tuple(updated)] = coefficient
    return answer


def canonical(polynomial: dict[tuple[int, ...], int]) -> tuple[tuple[tuple[int, ...], int], ...]:
    return tuple(sorted(polynomial.items()))


def main() -> int:
    vertex, colour = 0, 2
    left, right = c6.NBR[vertex]
    case0 = pipeline.cases_for(c6.X)[0]
    fixed = pipeline.max_fixable([
        (c6.X[index], source, target)
        for index, (source, target) in enumerate(case0)
    ])
    substitution = {c6.VAR[key]: sp.Integer(1) for key in fixed}
    entries = [
        sp.expand(c6.ch(vertex, left, c, colour).xreplace(substitution))
        for c in range(3) if c != colour
    ] + [
        sp.expand(c6.ch(vertex, right, c, colour).xreplace(substitution))
        for c in range(3) if c != colour
    ]
    a, b, c, d = entries
    theta = sp.expand(a * d - b * c)
    p_left = sp.expand(c6.P(vertex, left, colour).xreplace(substitution))
    p_right = sp.expand(c6.P(vertex, right, colour).xreplace(substitution))

    rows: list[dict[str, Any]] = []
    for colours in itertools.product(range(3), repeat=6):
        kind = profile(colours)
        word = "".join(map(str, colours))
        equation = sp.expand(
            c6.pm_sum(dict(enumerate(colours))).xreplace(substitution)
            - (1 if kind == (6,) else 0)
        )
        if equation != 0:
            rows.append({"word": word, "profile": list(kind), "equation": equation})
    if len(rows) != 729:
        raise RuntimeError("frozen C6 row census drift")
    variables = sorted(
        {symbol for row in rows for symbol in row["equation"].free_symbols}
        | p_left.free_symbols | p_right.free_symbols,
        key=sp.default_sort_key,
    )
    variable_index = {symbol: index for index, symbol in enumerate(variables)}
    groebner = sp.groebner([p_left, p_right], *variables, order="lex")
    reduced_rows: list[dict[str, Any]] = []
    for row in rows:
        quotients, remainder = groebner.reduce(row["equation"])
        replay = sp.expand(
            row["equation"] - remainder
            - sum(
                quotient * basis.as_expr()
                for quotient, basis in zip(quotients, groebner.polys, strict=True)
            )
        )
        if replay != 0:
            raise RuntimeError("P-kill reduction replay drift")
        reduced_rows.append({
            "word": row["word"],
            "profile": row["profile"],
            "remainder": sparse(remainder, variables),
            "groebner_quotients": [str(value) for value in quotients],
        })

    orientations = [
        {
            "name": "row_pair_aQ_plus_bX__cQ_plus_dX",
            "q_left": a,
            "q_right": c,
            "x_left": b,
            "x_right": d,
            "combination": "d*R_left - b*R_right = sign*theta*Q",
        },
        {
            "name": "row_pair_bQ_plus_aX__dQ_plus_cX",
            "q_left": b,
            "q_right": d,
            "x_left": a,
            "x_right": c,
            "combination": "c*R_left - a*R_right = -sign*theta*Q",
        },
    ]
    chord_records = []
    for chord in range(6):
        if chord == vertex or chord in (left, right):
            continue
        q_target = sp.expand(c6.P(vertex, chord, colour).xreplace(substitution))
        q_sparse = sparse(q_target, variables)
        matches = []
        for orientation in orientations:
            q_left_index = variable_index[orientation["q_left"]]
            q_right_index = variable_index[orientation["q_right"]]
            x_left_index = variable_index[orientation["x_left"]]
            x_right_index = variable_index[orientation["x_right"]]
            for sign in (1, -1):
                signed_q = q_sparse if sign == 1 else negate(q_sparse)
                left_q = multiply_by_variable(signed_q, q_left_index)
                right_q = multiply_by_variable(signed_q, q_right_index)
                left_by_x: dict[tuple[tuple[tuple[int, ...], int], ...], list[dict[str, Any]]] = defaultdict(list)
                right_by_x: dict[tuple[tuple[tuple[int, ...], int], ...], list[dict[str, Any]]] = defaultdict(list)
                for row in reduced_rows:
                    left_rest = divide_by_variable(
                        subtract(row["remainder"], left_q), x_left_index
                    )
                    if left_rest is not None:
                        left_by_x[canonical(left_rest)].append(row)
                    right_rest = divide_by_variable(
                        subtract(row["remainder"], right_q), x_right_index
                    )
                    if right_rest is not None:
                        right_by_x[canonical(right_rest)].append(row)
                for common in set(left_by_x) & set(right_by_x):
                    for row_left in left_by_x[common]:
                        for row_right in right_by_x[common]:
                            matches.append({
                                "orientation": orientation["name"],
                                "sign": sign,
                                "left_row": {
                                    "word": row_left["word"],
                                    "profile": row_left["profile"],
                                    "groebner_quotients": row_left["groebner_quotients"],
                                },
                                "right_row": {
                                    "word": row_right["word"],
                                    "profile": row_right["profile"],
                                    "groebner_quotients": row_right["groebner_quotients"],
                                },
                                "shared_remainder_quotient": [
                                    {"powers": list(powers), "coefficient": coefficient}
                                    for powers, coefficient in common
                                ],
                            })
        chord_records.append({
            "chord": chord,
            "target": str(q_target),
            "two_row_adjugate_matches": matches,
        })
    if any(record["two_row_adjugate_matches"] for record in chord_records):
        raise RuntimeError(
            "A two-row chord adjugate identity was found; promote it to a strict certificate instead of recording a negative audit."
        )

    payload = {
        "format": "krenn-c6-noncollapse-chord-adjugate-pair-audit-v1",
        "slot": {"vertex": vertex, "colour": colour, "neighbours": [left, right]},
        "theta_entries": [str(entry) for entry in entries],
        "theta": str(theta),
        "known_p_kills": [str(p_left), str(p_right)],
        "row_census": len(rows),
        "candidate_family": (
            "Two original gauge-fixed amplitude rows whose exact P-kill normal forms "
            "are an adjugate pair for theta(slot)*P(vertex,chord,colour), in either "
            "row/column orientation and either common Q sign."
        ),
        "chords": chord_records,
        "summary": {
            "chord_targets": len(chord_records),
            "two_row_adjugate_matches": 0,
        },
        "conclusion": {
            "established": (
                "The hard generic representative has no direct two-amplitude "
                "adjugate lift of a chord co-sum after the two known P-kills."
            ),
            "not_established": (
                "This excludes only the stated two-row template.  Longer syzygies, "
                "factor-sensitive identities, or other profile combinations remain open."
            ),
        },
        "sources": {
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "f9_pipeline_sha256": sha256(ROOT / "f9_pipeline.py"),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "receipt_payload_sha256": digest({
            "slot": [vertex, colour],
            "theta": str(theta),
            "chords": chord_records,
        }),
    }
    TARGET.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        "C6 NON-COLLAPSE CHORD ADJUGATE PAIR AUDIT VERIFIED: "
        f"{len(chord_records)} chord targets, no two-row matches"
    )
    print("manifest_sha256=" + sha256(TARGET))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
