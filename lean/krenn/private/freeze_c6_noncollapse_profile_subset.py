#!/usr/bin/env python3
"""Freeze a profile-selected subsystem of the C6 non-collapse slot branch.

The canonical branch has 579 deflated equation rows grouped by colouring
profile, followed by two adjugate P-kills and a determinant inverse.  This
tool selects whole profile blocks without changing their coefficients or
order, preserving the branch equations.  It is for sharply stated
ablation/strength tests; any solver outcome is only a discovery result until
an exact strict identity is replayed.
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

from c4_crux_freeze import write_msolve, write_singular_lift


PROFILE_NAMES = {
    "6": (6,),
    "5-1": (5, 1),
    "4-2": (4, 2),
    "4-1-1": (4, 1, 1),
    "3-2-1": (3, 2, 1),
}


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def as_polynomial(raw: list[list[object]], symbols: list[sp.Symbol]) -> sp.Expr:
    terms: dict[tuple[int, ...], int] = {}
    for coefficient, exponents in raw:
        key = tuple(int(value) for value in exponents)
        terms[key] = terms.get(key, 0) + int(coefficient)
    return sp.Poly.from_dict(terms, *symbols, domain=sp.ZZ).as_expr()


def profile_rows() -> list[tuple[str, tuple[int, ...]]]:
    rows = []
    accepted = set(PROFILE_NAMES.values())
    for colouring in itertools.product(range(3), repeat=6):
        kind = tuple(sorted(Counter(colouring).values(), reverse=True))
        if kind in accepted:
            rows.append(("".join(map(str, colouring)), kind))
    if len(rows) != 579:
        raise RuntimeError(f"profile row inventory drift: {len(rows)}")
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--profiles", nargs="+", choices=sorted(PROFILE_NAMES),
                        required=True)
    args = parser.parse_args()

    source = json.loads(args.source.read_text())
    raw_equations = source["equations"]
    names = source["variables"]
    symbols = [sp.Symbol(name) for name in names]
    labels = profile_rows()
    if len(raw_equations) != len(labels) + 3:
        raise RuntimeError("source profile branch shape drift")
    chosen_profiles = {PROFILE_NAMES[name] for name in args.profiles}
    selected = [index for index, (_word, kind) in enumerate(labels)
                if kind in chosen_profiles]
    selected += [579, 580, 581]
    selected.sort()
    core = {
        "variables": names,
        "equations": [raw_equations[index] for index in selected],
    }
    source_labels = {
        str(index + 1): labels[index][0] for index in selected if index < 579
    }
    source_labels.update({"580": "adjugate_P_kill_left",
                          "581": "adjugate_P_kill_right",
                          "582": "theta_inverse_branch"})
    payload = {
        "format": "krenn-c6-noncollapse-profile-subset-v1",
        "source_system_file_sha256": hashlib.sha256(args.source.read_bytes()).hexdigest(),
        "source_system_sha256": source.get("system_sha256"),
        "profiles": sorted(args.profiles),
        "profile_counts": dict(sorted(Counter(
            "-".join(map(str, labels[index][1])) for index in selected if index < 579
        ).items())),
        "branch_source_indices_1based": [580, 581, 582],
        "selected_source_indices_1based": [index + 1 for index in selected],
        "source_labels": source_labels,
        "statistics": {"generators": len(selected), "variables": len(symbols)},
        "system_sha256": digest(core),
        **core,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    system_path = args.output / "system.json"
    system_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    polynomials = [as_polynomial(raw_equations[index], symbols) for index in selected]
    write_msolve(args.output / "input_q.ms", symbols, polynomials, 0)
    write_msolve(args.output / "input_p32003.ms", symbols, polynomials, 32003)
    write_singular_lift(args.output / "lift.sing", symbols, polynomials)
    print(json.dumps({
        "profiles": payload["profiles"],
        "generators": len(selected),
        "system_sha256": payload["system_sha256"],
        "system_file_sha256": hashlib.sha256(system_path.read_bytes()).hexdigest(),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
