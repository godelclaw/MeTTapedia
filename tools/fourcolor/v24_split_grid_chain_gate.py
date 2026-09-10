#!/usr/bin/env python3
"""All-subset nested-chain gate on explicit two-dimensional open walls.

The preregistered bound is m <= 4*k*k+2*k+1 for a strictly nested chain
with m inclusions and complete edge cuts of size <= k. Every distinct width
threshold and every subset is checked for side lengths one through three. A Boolean
lattice dynamic program counts admissible visits, allowing jumps over
inadmissible subsets; it is not restricted to single-vertex valid moves.
These are colourable subcubic open walls, not closed counterexamples.
"""
import argparse
import json
from pathlib import Path

from v24_protected_mesh_gate import split_grid


def cut_sizes(adjacency):
    n = len(adjacency)
    neighbours = [sum(1 << w for w in adjacency[v]) for v in range(n)]
    cuts = [0] * (1 << n)
    for s in range(1, 1 << n):
        bit = s & -s
        v = bit.bit_length() - 1
        t = s ^ bit
        cuts[s] = cuts[t] + len(adjacency[v]) - 2 * (neighbours[v] & t).bit_count()
    return cuts


def longest_chain(valid):
    """Maximum number of valid sets in a nested chain, including endpoints."""
    dp = [0] * len(valid)
    dp[0] = int(valid[0])
    for s in range(1, len(valid)):
        bits, best = s, 0
        while bits:
            bit = bits & -bits
            best = max(best, dp[s ^ bit])
            bits ^= bit
        dp[s] = best + int(valid[s])
    return dp[-1]


def run():
    cases = []
    for r in range(1, 4):
        _, _, adjacency = split_grid(r, r)
        n = len(adjacency)
        cuts = cut_sizes(adjacency)
        widths = []
        for k in range(max(cuts) + 1):
            if k < r:
                assert all(min(s.bit_count(), n - s.bit_count()) <= 2*k*k+k
                           for s, cut in enumerate(cuts) if cut <= k)
            steps = longest_chain([cut <= k for cut in cuts]) - 1
            assert steps <= 4*k*k+2*k+1
            if k >= 1:
                assert (4*k*k+2*k+1).bit_length() <= 3 ** k
            widths.append(dict(width=k, maximum_steps=steps, polynomial_bound=4*k*k+2*k+1))
        cases.append(dict(side=r, vertices=n, subsets=len(cuts), widths=widths))
    return dict(schema='fourcolor-split-grid-chain-gate-v1', cases=cases,
                scope='all vertex subsets of the specified open split grids; not a closed minimal-counterexample class')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    result = run()
    if args.check:
        assert result == json.loads(args.check.read_text())
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
