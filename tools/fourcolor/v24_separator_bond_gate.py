#!/usr/bin/env python3
"""A vertex separator yields a complete connected edge bipartition.

Preregistered population: every labelled connected simple graph on 2--5
vertices, all ordered disjoint nonempty connected terminal sets A,B, and
every vertex separator X (including terminal vertices). Construct the
A-basin in G-X, restore A, and fill all complementary components except
the one containing B. Check both complete shores and the full edge cut.

Outcomes: construction_failure, degree_bound_failure, or passed. The bound
is maximum_degree * |X|, not |X|. No planar noose, branch decomposition,
colouring, or target counterexample-class assertion is tested here.
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter


def component(adj, allowed, root):
    assert root in allowed
    seen, todo = {root}, [root]
    while todo:
        v = todo.pop()
        for w in adj[v] & allowed - seen:
            seen.add(w)
            todo.append(w)
    return seen


def audit():
    counts = Counter()
    first_filled = None
    for n in range(2, 6):
        full = set(range(n))
        pairs = list(itertools.combinations(range(n), 2))
        subsets = [{v for v in full if m >> v & 1} for m in range(1 << n)]
        for mask in range(1 << len(pairs)):
            edges = [e for i, e in enumerate(pairs) if mask >> i & 1]
            adj = [set() for _ in full]
            for u, v in edges:
                adj[u].add(v)
                adj[v].add(u)
            if component(adj, full, 0) != full:
                continue
            counts[f"graphs_{n}"] += 1
            connected = [s for s in subsets if s and component(adj, s, min(s)) == s]
            components = []
            for X in subsets:
                unused, parts = full - X, []
                while unused:
                    part = component(adj, unused, min(unused))
                    parts.append(part)
                    unused -= part
                components.append(parts)
            degree = max(map(len, adj))
            for A in connected:
                for B in connected:
                    if A & B:
                        continue
                    for X, parts in zip(subsets, components):
                        if any(part & A and part & B for part in parts):
                            continue
                        counts["separators"] += 1
                        counts["terminal_overlap"] += bool(X & (A | B))
                        basin = A | set().union(*(p for p in parts if p & A))
                        outside = component(adj, full - basin, min(B))
                        shore = full - outside
                        boundary = [e for e in edges if (e[0] in shore) != (e[1] in shore)]
                        assert A <= shore and B <= outside, "construction_failure"
                        assert component(adj, shore, min(A)) == shore, "construction_failure"
                        assert all(set(e) & X for e in boundary), "construction_failure"
                        assert len(boundary) <= degree * len(X), "degree_bound_failure"
                        counts["filled"] += shore != basin
                        counts["bound_tight"] += len(boundary) == degree * len(X)
                        if shore != basin and first_filled is None:
                            first_filled = dict(n=n, edges=edges, A=sorted(A), B=sorted(B),
                                                X=sorted(X), basin=sorted(basin),
                                                shore=sorted(shore), boundary=boundary)
    assert [counts[f"graphs_{n}"] for n in range(2, 6)] == [1, 4, 38, 728]
    return dict(schema="fourcolor-v24-separator-bond-v1", counts=dict(counts),
                first_filled=first_filled, outcome="passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only")
    args = parser.parse_args()
    result = json.loads(json.dumps(audit()))
    if args.verify_only:
        with open(args.verify_only) as stream:
            assert json.load(stream) == result, "receipt_mismatch"
        print("fixed-population replay passed")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
