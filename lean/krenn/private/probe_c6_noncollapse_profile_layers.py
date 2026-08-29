#!/usr/bin/env python3
"""Freeze bounded balanced-profile probes for one C6 non-collapse slot.

The full slot-0 branch consists of all 729 gauge-fixed C6 equations, the two
adjugate P-kills, and a Rabinowitsch inverse for the slot determinant.  This
tool keeps the lower layers (mono, one-defect, and two-defect) and chooses a
subset of the three balanced profiles.  Its only purpose is to identify a
small, exact target for a later certificate search; a modular GB verdict is
never treated as a proof object.
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
from c4_crux_freeze import canonical_polynomial, write_msolve, write_singular_lift
from engine_fingerprint import ROOT, source_manifest


LOWER_PROFILES = {(6,), (5, 1), (4, 2), (4, 1, 1)}
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
    parser.add_argument("--include", nargs="*", choices=sorted(BALANCED),
                        default=[])
    parser.add_argument("--prime", type=int, default=32003)
    parser.add_argument("--vertex", type=int, choices=range(6), default=0)
    parser.add_argument("--colour", type=int, choices=range(3), default=0)
    args = parser.parse_args()

    selected_profiles = LOWER_PROFILES | {
        BALANCED[name] for name in args.include
    }
    case = pipeline.cases_for(c6.X)[0]
    chosen = [(c6.X[index], colours[0], colours[1])
              for index, colours in enumerate(case)]
    fixed = pipeline.max_fixable(chosen)
    substitution = {c6.VAR[key]: sp.Integer(1) for key in fixed}

    selected: list[tuple[str, sp.Expr]] = []
    counts: Counter[tuple[int, ...]] = Counter()
    for colours in itertools.product(range(3), repeat=6):
        kind = profile(colours)
        if kind not in selected_profiles:
            continue
        polynomial = sp.expand(c6.pm_sum(dict(enumerate(colours)))
                             .xreplace(substitution))
        if kind == (6,):
            polynomial -= 1
        if polynomial == 0:
            raise ValueError(f"zero frozen row at {colours}")
        selected.append(("".join(map(str, colours)), polynomial))
        counts[kind] += 1

    vertex, colour = args.vertex, args.colour
    left, right = c6.NBR[vertex]
    determinant = sp.expand(c6.theta_det(vertex, colour).xreplace(substitution))
    left_kill = sp.expand(c6.P(vertex, left, colour).xreplace(substitution))
    right_kill = sp.expand(c6.P(vertex, right, colour).xreplace(substitution))
    inverse = sp.Symbol(f"theta_{vertex}_{colour}_inv")
    branch = [left_kill, right_kill, sp.expand(determinant * inverse - 1)]
    generators = [poly for _, poly in selected] + branch
    variables = sorted(
        {symbol for poly in generators for symbol in poly.free_symbols},
        key=sp.default_sort_key,
    )
    system = {
        "variables": [str(symbol) for symbol in variables],
        "equations": [canonical_polynomial(poly, variables) for poly in generators],
    }
    payload = {
        "format": "krenn-c6-noncollapse-profile-probe-v1",
        "slot": {"vertex": vertex, "colour": colour, "neighbours": [left, right]},
        "balanced_profiles": sorted(args.include),
        "profile_counts": {"-".join(map(str, key)): value
                           for key, value in sorted(counts.items())},
        "selected_colouring_sha256": digest([word for word, _ in selected]),
        "statistics": {
            "equations_before_branch": len(selected),
            "branch_equations": len(branch),
            "generators": len(generators),
            "variables": len(variables),
        },
        "system_sha256": digest(system),
        "source_manifest": source_manifest(
            "probe_c6_noncollapse_profile_layers",
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
    write_msolve(args.output / "input_q.ms", variables, generators, 0)
    write_msolve(args.output / f"input_p{args.prime}.ms", variables, generators,
                 args.prime)
    write_singular_lift(args.output / "lift.sing", variables, generators)
    print(json.dumps({
        "profiles": payload["balanced_profiles"],
        "statistics": payload["statistics"],
        "system_sha256": payload["system_sha256"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
