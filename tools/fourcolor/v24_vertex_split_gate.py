#!/usr/bin/env python3
"""Preregistered vertex-splitting gate, including terminal capacities.

All labelled simple graphs on 2--4 vertices; all ordered nonempty disjoint
terminal pairs; thresholds 1 through n+1. Use unit vertex gates, threshold
capacity on every ambient adjacency and terminal connector. Compare with
exhaustive simple-path packing and vertex separators in the original graph.
If the split cut has value below the threshold, extract its crossing vertex
gates and check they meet every terminal-to-terminal path. Otherwise check
that at least threshold many vertex-disjoint paths actually exist.

Outcomes: packing_separator_mismatch, low_cut_failure, high_flow_failure,
passed. No planarity or non-colourability assumption is used.
"""

import argparse
import itertools
import json
from collections import Counter
from v24_integer_flow_gate import solve


def path_masks(adj, A, B):
    masks = set()

    def visit(u, seen):
        if u in B:
            masks.add(seen)
            return
        for v in adj[u]:
            if not (seen >> v & 1):
                visit(v, seen | 1 << v)

    for a in A:
        visit(a, 1 << a)
    return masks


def audit():
    counts = Counter()
    for n in range(2, 5):
        pairs = list(itertools.combinations(range(n), 2))
        subsets = [{u for u in range(n) if bits >> u & 1} for bits in range(1, 1 << n)]
        for bits in range(1 << len(pairs)):
            edges = [e for i, e in enumerate(pairs) if bits >> i & 1]
            adj = [set() for _ in range(n)]
            for u, v in edges:
                adj[u].add(v)
                adj[v].add(u)
            counts[f"graphs_{n}"] += 1
            for A in subsets:
                for B in subsets:
                    if A & B:
                        continue
                    paths = path_masks(adj, A, B)
                    best = {0: 0}
                    for occupied in range(1 << n):
                        if occupied not in best:
                            continue
                        for p in paths:
                            if not occupied & p:
                                best[occupied | p] = max(best.get(occupied | p, 0), best[occupied] + 1)
                    packing = max(best.values())
                    separator = min(X.bit_count() for X in range(1 << n)
                                    if all(X & p for p in paths))
                    assert packing == separator, "packing_separator_mismatch"
                    for k in range(1, n + 2):
                        size = 2 * n + 2
                        cap = [[0] * size for _ in range(size)]
                        for u in range(n):
                            entry, exit = 2 * u + 1, 2 * u + 2
                            cap[entry][exit] = 1
                            if u in A:
                                cap[0][entry] = k
                            if u in B:
                                cap[exit][-1] = k
                            for v in adj[u]:
                                cap[exit][2 * v + 1] = k
                        result = solve(size, (), cap, exhaustive=False)
                        counts["instances"] += 1
                        if result["value"] >= k:
                            assert packing >= k, "high_flow_failure"
                            used = set()
                            for route in result["decomposition"][:k]:
                                assert route[0] == 0 and route[-1] == size - 1
                                body = route[1:-1]
                                assert len(body) % 2 == 0
                                vertices = [(x - 1) // 2 for x in body[::2]]
                                assert body == [z for u in vertices for z in (2 * u + 1, 2 * u + 2)]
                                assert vertices[0] in A and vertices[-1] in B
                                assert all(v in adj[u] for u, v in zip(vertices, vertices[1:]))
                                assert not used.intersection(vertices), "shared_vertex_failure"
                                used.update(vertices)
                            counts["high"] += 1
                        else:
                            S = set(result["reached"])
                            X = sum(1 << u for u in range(n)
                                    if 2 * u + 1 in S and 2 * u + 2 not in S)
                            assert X.bit_count() == result["value"] < k, "low_cut_failure"
                            assert all(X & p for p in paths), "low_cut_failure"
                            counts["low"] += 1
    assert [counts[f"graphs_{n}"] for n in range(2, 5)] == [2, 8, 64]
    return dict(schema="fourcolor-v24-vertex-split-v1", counts=dict(counts), outcome="passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only")
    args = parser.parse_args()
    result = audit()
    if args.verify_only:
        with open(args.verify_only) as stream:
            assert json.load(stream) == result, "receipt_mismatch"
        print("fixed vertex-split population replay passed")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
