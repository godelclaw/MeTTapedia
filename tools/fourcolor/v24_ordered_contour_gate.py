#!/usr/bin/env python3
"""First-hit ordering and simultaneous monotone thinning for contour meshes.

Pre-registered outcomes: reject a non-increasing first-hit sequence; reject
an invalid extracted ordered submesh; reject a repeated rank signature or
an Erdős--Szekeres bound violation. Otherwise retain the finite controls.
The spherical population is the existing eight full-ambient GP receipts,
independently rechecked by their verifier. Synthetic depth traces explicitly
test repeated encounters; they are not asserted to be spherical maps.
No colouring, counterexample instance, or optimal branchwidth is presumed.
"""

import argparse
import itertools
import json
import random
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_contour_mesh_gate import verify_archive


def longest(rows, directions):
    n = len(rows[0]) if rows else 0
    chains = [[j] for j in range(n)]
    for j in range(n):
        for i in range(j):
            if all((r[i] < r[j]) == d for r, d in zip(rows, directions)):
                if len(chains[i]) + 1 > len(chains[j]):
                    chains[j] = chains[i] + [j]
    return chains


def rank_check(rows):
    a, n = len(rows), len(rows[0])
    assert all(len(set(r)) == n for r in rows)
    families = [longest(rows, ds) for ds in itertools.product((False, True), repeat=a)]
    signatures = [tuple(len(cs[j]) for cs in families) for j in range(n)]
    assert len(set(signatures)) == n
    best = max(len(c) for cs in families for c in cs)
    assert n <= best ** (2 ** a)
    return best


def finite_controls():
    counts = {}
    for a, cap in ((1, 7), (2, 5), (3, 4)):
        count = 0
        for n in range(1, cap + 1):
            perms = list(itertools.permutations(range(n)))
            for rows in itertools.product(perms, repeat=a):
                rank_check(rows)
                count += 1
        counts[str(a)] = count
    rng = random.Random(7319)
    for a, n, repetitions in ((2, 17, 30), (3, 257, 4)):
        for _ in range(repetitions):
            rows = [rng.sample(range(n), n) for _ in range(a)]
            assert rank_check(rows) >= 3
    # Equality at the strict one-coordinate threshold does NOT force length 3.
    assert rank_check([[1, 0, 3, 2]]) == 2
    traces, reentries = 0, 0
    for depth in range(1, 5):
        pending = [(0,)]
        while pending:
            trace = pending.pop()
            if trace[-1] == depth:
                hits = [trace.index(i) for i in range(depth + 1)]
                assert all(x < y for x, y in zip(hits, hits[1:]))
                traces += 1
                reentries += len(set(trace)) < len(trace)
            if len(trace) < 12:
                pending.extend(trace + (j,) for j in (trace[-1] - 1, trace[-1] + 1)
                               if 0 <= j <= depth)
    # Arbitrary choices at repeated encounters need not respect depth order.
    trace, arbitrary = [0, 1, 0, 1, 2], [2, 1, 4]
    assert [trace[t] for t in arbitrary] == [0, 1, 2]
    assert not all(x < y for x, y in zip(arbitrary, arbitrary[1:]))
    return {"permutation_families": counts, "threshold_random_cases": 34,
            "depth_traces": traces, "traces_with_reentry": reentries,
            "strict_threshold_negative": True, "arbitrary_hit_negative": True}


def sphere_controls(archive):
    verify_archive(archive)
    output = []
    for receipt in archive["receipts"]:
        lo, hi = receipt["selected"]
        rows = [r["cycle"] for r in receipt["contours"][lo:hi + 1]]
        paths = receipt["paths"]
        branches = [[next(v for v in p if v in row) for p in paths] for row in rows]
        for j, p in enumerate(paths):
            hits = [p.index(bs[j]) for bs in branches]
            assert all(x < y for x, y in zip(hits, hits[1:]))
        positions = [[row.index(v) for v in bs] for row, bs in zip(rows, branches)]
        keep, directions = list(range(len(paths))), []
        for row in positions:
            restricted = [[row[j] for j in keep]]
            choices = [(c, d) for d in (False, True)
                       for c in longest(restricted, [d])]
            choice, direction = max(choices, key=lambda cd: len(cd[0]))
            keep = [keep[j] for j in choice]
            directions.append(direction)
        assert keep and keep == sorted(set(keep))
        selected = [[bs[j] for j in keep] for bs in branches]
        assert len(set(v for bs in selected for v in bs)) == len(rows) * len(keep)
        for row, bs, direction in zip(rows, selected, directions):
            path = row if direction else row[::-1]
            indices = [path.index(v) for v in bs]
            assert all(x < y for x, y in zip(indices, indices[1:]))
        output.append({"frequency": receipt["frequency"], "rows": len(rows),
                       "columns_before": len(paths), "columns_after": len(keep),
                       "selected_columns": keep, "row_directions": directions})
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {"schema": "fourcolor-v24-ordered-contour-v1",
              "finite": finite_controls(),
              "spheres": sphere_controls(json.loads(args.archive.read_text()))}
    if args.output:
        atomic_write_json(args.output, result)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
