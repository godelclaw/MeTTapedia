#!/usr/bin/env python3
"""Exact finite target analysis for C6 non-collapse P-kills.

The doily potential endpoint needs a set F of dead co-sums such that there
is a vertex potential s with nonzero total and s_u + s_v = 0 off F.  This
script works over Q and identifies the smallest such completion of the two
cycle P-kills supplied by a non-collapse slot at vertex 0.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path

import sympy as sp


VERTICES = range(6)
EDGES = list(itertools.combinations(VERTICES, 2))
CYCLE = {
    (0, 4), (0, 5), (1, 2), (1, 3), (2, 5), (3, 4),
}
SEED = {(0, 4), (0, 5)}
EXPECTED_EXTRA = ((0, 1), (0, 2), (0, 3))


def potential_basis(dead: set[tuple[int, int]]) -> list[list[int]]:
    """Exact Q-basis of potentials zero on every edge outside ``dead``."""
    rows = []
    for left, right in EDGES:
        if (left, right) not in dead:
            row = [0] * 6
            row[left] = row[right] = 1
            rows.append(row)
    return [list(map(int, vector)) for vector in sp.Matrix(rows).nullspace()]


def is_fatal(dead: set[tuple[int, int]]) -> tuple[bool, list[list[int]]]:
    basis = potential_basis(dead)
    return any(sum(vector) != 0 for vector in basis), basis


def main() -> int:
    cycle_masks_checked = 0
    for size in range(len(CYCLE) + 1):
        for subset in itertools.combinations(sorted(CYCLE), size):
            fatal, _basis = is_fatal(set(subset))
            if fatal:
                raise RuntimeError(f"cycle-only potential unexpectedly fatal: {subset}")
            cycle_masks_checked += 1

    remaining = [edge for edge in EDGES if edge not in SEED]
    minimal_extensions: list[tuple[tuple[int, int], ...]] = []
    for size in range(len(remaining) + 1):
        hits = []
        for extension in itertools.combinations(remaining, size):
            fatal, _basis = is_fatal(SEED | set(extension))
            if fatal:
                hits.append(extension)
        if hits:
            minimal_extensions = hits
            break
    if minimal_extensions != [EXPECTED_EXTRA]:
        raise RuntimeError(
            "unexpected minimal star completion: "
            f"{minimal_extensions!r}"
        )
    fatal, basis = is_fatal(SEED | set(EXPECTED_EXTRA))
    if not fatal or basis != [[1, 0, 0, 0, 0, 0]]:
        raise RuntimeError(f"unexpected star basis: {basis!r}")

    receipt = {
        "format": "krenn-c6-potential-targets-v1",
        "field": "Q",
        "cycle_edges": [list(edge) for edge in sorted(CYCLE)],
        "cycle_masks_checked": cycle_masks_checked,
        "noncollapse_vertex0_seed": [list(edge) for edge in sorted(SEED)],
        "minimum_extra_kills": len(EXPECTED_EXTRA),
        "unique_minimum_extra": [list(edge) for edge in EXPECTED_EXTRA],
        "star_potential_basis": basis,
        "conclusion": (
            "cycle-only P-kills cannot support a nonzero-mean potential; "
            "the unique smallest completion of the vertex-0 adjacent pair "
            "is the three remaining star edges"
        ),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    output = Path(__file__).with_name("c6_potential_target_receipt.json")
    output.write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print("C6 POTENTIAL TARGETS VERIFIED")
    print("receipt_sha256=" + hashlib.sha256(output.read_bytes()).hexdigest())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
