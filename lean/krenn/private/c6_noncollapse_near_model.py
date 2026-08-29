#!/usr/bin/env python3
"""Exact regression for the C6 non-collapse harvest layer.

The three diagonal perfect matchings are the standard colour-zero/one/two
matching basis.  Adding two off-diagonal channels creates a genuine
non-collapse determinant at slot ``(vertex 0, colour 0)``.  The resulting
assignment satisfies every monochromatic, one-defect, and two-defect equation
and misses exactly three balanced equations.

This is not a witness: the three remaining equations are nonzero.  It is a
falsification guard.  Any proposed non-collapse harvest theorem that omits
all of those balanced profiles is false.  In particular, it prevents an
accidental revival of a claim that the L0--L2 layers alone close the
non-collapse branch.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import itertools
import json
import sys
from collections import Counter
from pathlib import Path

import sympy as sp

SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

import c6_collapse_attack as c6


MATCHINGS = [
    ((0, 1), (2, 3), (4, 5)),
    ((0, 2), (1, 4), (3, 5)),
    ((0, 3), (1, 5), (2, 4)),
]
EXPECTED_SYMBOLIC = {
    "002121": "1",
    "120002": "a",
    "210010": "b",
}


def assignment(a: sp.Expr, b: sp.Expr) -> dict[sp.Symbol, sp.Expr]:
    values: dict[sp.Symbol, sp.Expr] = {symbol: sp.Integer(0)
                                        for symbol in c6.VAR.values()}
    for colour, matching in enumerate(MATCHINGS):
        for edge in matching:
            values[c6.VAR[(edge, colour, colour)]] = sp.Integer(1)
    # theta_0(0) = [[w_04_10, w_05_10], [w_04_20, w_05_20]] has det a*b.
    values[c6.ch(0, 4, 1, 0)] = a
    values[c6.ch(0, 5, 2, 0)] = b
    return values


def residuals(values: dict[sp.Symbol, sp.Expr]) -> dict[str, sp.Expr]:
    result: dict[str, sp.Expr] = {}
    for colouring in itertools.product(range(3), repeat=6):
        equation = c6.pm_sum(dict(enumerate(colouring)))
        if len(set(colouring)) == 1:
            equation -= 1
        residual = sp.expand(equation.subs(values))
        if residual != 0:
            result["".join(map(str, colouring))] = residual
    return result


def profile(colouring: str) -> tuple[int, ...]:
    return tuple(sorted(Counter(colouring).values(), reverse=True))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    a, b = sp.symbols("a b")
    symbolic = residuals(assignment(a, b))
    symbolic_text = {key: str(value) for key, value in symbolic.items()}
    if symbolic_text != EXPECTED_SYMBOLIC:
        raise RuntimeError(f"symbolic residual drift: {symbolic_text}")

    numeric = residuals(assignment(sp.Integer(1), sp.Integer(1)))
    if set(numeric) != set(EXPECTED_SYMBOLIC) or any(value != 1
                                                       for value in numeric.values()):
        raise RuntimeError(f"numeric residual drift: {numeric}")

    numeric_values = assignment(sp.Integer(1), sp.Integer(1))
    theta = sp.expand(c6.theta_det(0, 0).subs(numeric_values))
    if theta != 1:
        raise RuntimeError(f"slot (0,0) stopped being non-collapse: {theta}")
    live_cosums = [edge for edge in c6.EDGES
                    if sp.expand(c6.P(*edge, 0).subs(numeric_values)) != 0]
    if live_cosums != [(0, 1), (2, 3), (4, 5)]:
        raise RuntimeError(f"unexpected colour-zero co-sums: {live_cosums}")

    source = SHARED / "allcollapse_case_artifacts/case_0/system.json"
    receipt = {
        "format": "krenn-c6-noncollapse-near-model-v1",
        "source_system_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "theta_slot_0_0": int(theta),
        "live_colour_zero_cosums": ["".join(map(str, edge)) for edge in live_cosums],
        "residual_equations": symbolic_text,
        "residual_profiles": {
            key: list(profile(key)) for key in symbolic_text
        },
        "all_other_colourings_vanish": len(symbolic_text) == 3,
        "interpretation": (
            "A genuine non-collapse slot survives all non-balanced layers; "
            "the three listed balanced equations are mandatory regression "
            "obligations for any harvest theorem."
        ),
    }
    encoded = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt is not None:
        args.receipt.write_text(encoded)
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
