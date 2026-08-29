#!/usr/bin/env python3
"""Freeze one exact C6 case-0 adjugate non-collapse branch.

The branch retains the 729 original gauge-fixed equations, adds an inverse
for one slot determinant, and adds the two P-kills forced by its adjugate
identity.  It intentionally contains no all-collapse determinant equations.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp


SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

import c6_collapse_attack as c6  # noqa: E402
import f9_pipeline as pipeline  # noqa: E402
from c4_crux_freeze import canonical_polynomial, write_msolve  # noqa: E402
from engine_fingerprint import ROOT, source_manifest  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--vertex", type=int, default=0)
    parser.add_argument("--colour", type=int, default=0)
    parser.add_argument("--prime", type=int, default=32003)
    args = parser.parse_args()
    if args.vertex not in range(6) or args.colour not in range(3):
        raise ValueError("vertex/colour out of range")

    case = pipeline.cases_for(c6.X)[0]
    chosen = [(c6.X[index], colours[0], colours[1])
              for index, colours in enumerate(case)]
    fixed = pipeline.max_fixable(chosen)
    substitution = {c6.VAR[key]: sp.Integer(1) for key in fixed}

    base = [sp.expand(polynomial.xreplace(substitution))
            for polynomial in c6.system()]
    if len(base) != 729 or len(set(base)) != 729:
        raise ValueError("base system gauge substitution drift")
    vertex, colour = args.vertex, args.colour
    left_neighbour, right_neighbour = c6.NBR[vertex]
    determinant = sp.expand(c6.theta_det(vertex, colour).xreplace(substitution))
    left_kill = sp.expand(c6.P(vertex, left_neighbour, colour).xreplace(substitution))
    right_kill = sp.expand(c6.P(vertex, right_neighbour, colour).xreplace(substitution))
    inverse = sp.Symbol(f"theta_{vertex}_{colour}_inv")
    inverse_equation = sp.expand(determinant * inverse - 1)
    if determinant == 0 or left_kill == 0 or right_kill == 0:
        raise ValueError("unexpected zero branch polynomial")
    generators = sorted({*base, left_kill, right_kill, inverse_equation},
                        key=sp.default_sort_key)
    variables = sorted(
        {symbol for polynomial in generators for symbol in polynomial.free_symbols},
        key=sp.default_sort_key,
    )
    system = {
        "variables": [str(symbol) for symbol in variables],
        "equations": [canonical_polynomial(polynomial, variables)
                      for polynomial in generators],
    }
    system_sha256 = hashlib.sha256(json.dumps(
        system, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    payload = {
        "format": "krenn-frozen-polynomial-system-v1",
        "problem": {
            "mixed_support": [list(edge) for edge in c6.X],
            "case_index": 0,
            "case": [list(colours) for colours in case],
            "branch": "adjugate_noncollapse_slot",
            "slot": {"vertex": vertex, "colour": colour,
                     "neighbours": [left_neighbour, right_neighbour]},
            "gauge_fixed_entries": [[list(edge), left, right]
                                    for edge, left, right in fixed],
            "determinant": str(determinant),
            "left_kill": str(left_kill),
            "right_kill": str(right_kill),
            "inverse": str(inverse),
        },
        "statistics": {
            "base_equations": len(base),
            "extra_branch_equations": 3,
            "distinct_generators": len(generators),
            "variables": len(variables),
        },
        "system_sha256": system_sha256,
        "source_manifest": source_manifest(
            "freeze_c6_case0_noncollapse_slot",
            sources=[ROOT / "c6_collapse_attack.py", ROOT / "f9_pipeline.py",
                     ROOT / "krenn_exact.py", ROOT / "c4_crux_freeze.py",
                     Path(__file__)],
        ),
        **system,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    system_path = args.output / "system.json"
    system_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    polynomials = [sp.Poly.from_dict(
        {tuple(exponents): int(coefficient) for coefficient, exponents in row},
        *variables,
        domain=sp.ZZ,
    ).as_expr() for row in system["equations"]]
    write_msolve(args.output / f"input_p{args.prime}.ms", variables,
                 polynomials, args.prime)
    write_msolve(args.output / "input_q.ms", variables, polynomials, 0)
    print(
        f"C6 noncollapse slot u={vertex} k={colour}: "
        f"vars={len(variables)} generators={len(generators)}"
    )
    print("system_sha256=" + system_sha256)
    print("system_file_sha256=" + sha256(system_path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
