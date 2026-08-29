#!/usr/bin/env python3
"""Freeze a homogeneous C6 non-collapse P-harvest membership target.

For one determinant-nonzero slot, the adjugate layer supplies the two cycle
P-kills.  The doily endpoint needs the three remaining (chord) P-kills at
that vertex.  This script freezes the homogeneous lower-plus-321 equations,
adds the two known P-kills, and asks whether

    theta(slot) * P(slot.vertex, chord, slot.colour)

lies in their ideal.  Such an identity is directly useful: on the
non-collapse branch theta is nonzero, hence it kills the indicated chord P.
No solver verdict is a proof object; the generated payload is intended for a
separate exact or modular Macaulay certificate probe.
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
import f9_pipeline as pipeline
from c4_crux_freeze import canonical_polynomial
from engine_fingerprint import ROOT, source_manifest


LOWER_PROFILES = {(5, 1), (4, 2), (4, 1, 1)}
BALANCED = {
    "33": (3, 3),
    "321": (3, 2, 1),
    "222": (2, 2, 2),
}


def profile(colours: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(Counter(colours).values(), reverse=True))


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--vertex", type=int, default=0, choices=range(6))
    parser.add_argument("--colour", type=int, default=0, choices=range(3))
    parser.add_argument("--chord", type=int, default=1, choices=range(6))
    parser.add_argument("--target-kind", choices=("chord", "star-sum", "theta-square"),
                        default="chord")
    parser.add_argument("--include", nargs="+", choices=sorted(BALANCED),
                        default=["321"])
    args = parser.parse_args()
    u, k, chord = args.vertex, args.colour, args.chord
    if chord == u or chord in c6.NBR[u]:
        parser.error("--chord must be a non-cycle neighbour of --vertex")

    case = pipeline.cases_for(c6.X)[0]
    chosen = [(c6.X[index], colours[0], colours[1])
              for index, colours in enumerate(case)]
    fixed = pipeline.max_fixable(chosen)
    substitution = {c6.VAR[key]: sp.Integer(1) for key in fixed}

    profiles = LOWER_PROFILES | {BALANCED[name] for name in args.include}
    selected: list[tuple[str, sp.Expr]] = []
    counts: Counter[tuple[int, ...]] = Counter()
    for colours in itertools.product(range(3), repeat=6):
        kind = profile(colours)
        if kind not in profiles:
            continue
        polynomial = sp.expand(c6.pm_sum(dict(enumerate(colours)))
                             .xreplace(substitution))
        if polynomial == 0:
            raise ValueError(f"zero frozen row at {colours}")
        selected.append(("".join(map(str, colours)), polynomial))
        counts[kind] += 1

    left, right = c6.NBR[u]
    generators = [poly for _word, poly in selected]
    generators.extend([
        sp.expand(c6.P(u, left, k).xreplace(substitution)),
        sp.expand(c6.P(u, right, k).xreplace(substitution)),
    ])
    if args.target_kind == "chord":
        target = sp.expand(c6.theta_det(u, k).xreplace(substitution)
                           * c6.P(u, chord, k).xreplace(substitution))
        target_description = "theta(slot) * P(vertex,chord,colour)"
    elif args.target_kind == "star-sum":
        target = sp.expand(sum(
            c6.ch(u, v, k, k) * c6.P(u, v, k)
            for v in range(6) if v != u
        ).xreplace(substitution))
        target_description = "sum_{e incident to vertex} D_e(colour) * P_e(colour)"
    else:
        determinant = sp.expand(c6.theta_det(u, k).xreplace(substitution))
        target = sp.expand(determinant ** 2)
        target_description = "theta(slot)^2 (homogeneous saturation target)"
    variables = sorted(
        {symbol for polynomial in generators + [target]
         for symbol in polynomial.free_symbols},
        key=sp.default_sort_key,
    )
    system = {
        "variables": [str(symbol) for symbol in variables],
        "equations": [canonical_polynomial(poly, variables)
                      for poly in generators],
        "target": canonical_polynomial(target, variables),
    }
    payload = {
        "format": "krenn-c6-noncollapse-p-membership-v1",
        "slot": {"vertex": u, "colour": k, "neighbours": [left, right]},
        "target_kind": args.target_kind,
        "target_chord": chord if args.target_kind == "chord" else None,
        "balanced_profiles": sorted(args.include),
        "target_description": target_description,
        "profile_counts": {"-".join(map(str, key)): value
                           for key, value in sorted(counts.items())},
        "selected_colouring_sha256": digest([word for word, _ in selected]),
        "statistics": {
            "equations_before_kills": len(selected),
            "known_p_kills": 2,
            "generators": len(generators),
            "variables": len(variables),
        },
        "system_sha256": digest(system),
        "source_manifest": source_manifest(
            "freeze_c6_noncollapse_p_membership",
            sources=[ROOT / "c6_collapse_attack.py", ROOT / "f9_pipeline.py",
                     ROOT / "krenn_exact.py", ROOT / "c4_crux_freeze.py",
                     Path(__file__)],
        ),
        **system,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "system.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps({
        "slot": payload["slot"],
        "target_kind": payload["target_kind"],
        "target_chord": payload["target_chord"],
        "statistics": payload["statistics"],
        "system_sha256": payload["system_sha256"],
    }, sort_keys=True))


if __name__ == "__main__":
    raise SystemExit(main())
