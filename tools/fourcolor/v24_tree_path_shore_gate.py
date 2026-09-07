#!/usr/bin/env python3
"""Preregistered tree-path shore gate, independent of colouring.

Exhaust labelled trees through six vertices and all ordered endpoint pairs.
Deleting path edge i must put precisely path positions 0..i on the start
side. These sides must be strictly nested, with at least i+1 vertices
inside and length-i outside. Outcomes: calibration, partition, nesting,
cardinality failure, or passed. Spherical order/full-cut checks live in
the separate tree-cotree gate; these controls are not counterexamples.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_fundamental_parity_gate import root_tree


def run():
    rows = []
    for n in range(1, 7):
        trees = paths_checked = cuts = comparisons = 0
        pairs = list(itertools.combinations(range(n), 2))
        for edges in itertools.combinations(pairs, n - 1):
            if len(root_tree(n, edges, 0)[0]) != n:
                continue
            trees += 1
            adj = [[] for _ in range(n)]
            for e, (u, v) in enumerate(edges):
                adj[u].append((v, e))
                adj[v].append((u, e))
            for start in range(n):
                routes = {start: ([start], [])}
                queue = [start]
                for u in queue:
                    for v, e in adj[u]:
                        if v not in routes:
                            vs, es = routes[u]
                            routes[v] = (vs + [v], es + [e])
                            queue.append(v)
                for finish in range(n):
                    vertices, path_edges = routes[finish]
                    previous = set()
                    for i, removed in enumerate(path_edges):
                        side, queue = {start}, [start]
                        for u in queue:
                            for v, e in adj[u]:
                                if e != removed and v not in side:
                                    side.add(v)
                                    queue.append(v)
                        assert [v in side for v in vertices] == [
                            j <= i for j in range(len(vertices))], "partition_failure"
                        assert len(side) >= i + 1, "cardinality_failure"
                        assert n - len(side) >= len(path_edges) - i, "cardinality_failure"
                        if i:
                            assert previous < side, "nesting_failure"
                            comparisons += 1
                        previous = side
                        cuts += 1
                    paths_checked += 1
        assert trees == (1 if n == 1 else n ** (n - 2)), "calibration_failure"
        rows.append(dict(vertices=n, trees=trees, paths=paths_checked,
                         cuts=cuts, comparisons=comparisons))
    return dict(schema="fourcolor-v24-tree-path-shore-v1", outcome="passed", rows=rows)


def raw_decomposition_control():
    """Finite comb calibration before constructing the raw consumer adapter."""
    checked = 0
    for n in range(3, 33):
        graphs = [list(zip(range(n), list(range(1, n)) + [0]))]
        if n <= 8:
            graphs.append(list(itertools.combinations(range(n), 2)))
        for edges in graphs:
            labels = list(range(len(edges)))
            root, left, *right = labels
            assert right and [root, left] + right == labels
            # Right-comb cuts are single leaves and suffixes of the right list.
            cuts = [{e} for e in labels] + [set(right[i:]) for i in range(len(right))]
            for cut in cuts:
                inside = {v for e in cut for v in edges[e]}
                outside = {v for e in set(labels) - cut for v in edges[e]}
                assert len(inside & outside) <= n, "raw_width_failure"
                checked += 1
    return dict(families="cycles3..32, complete3..8", cuts=checked, outcome="passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-only", type=Path)
    parser.add_argument("--raw-control", action="store_true")
    args = parser.parse_args()
    result = raw_decomposition_control() if args.raw_control else run()
    if args.verify_only:
        assert result == json.loads(args.verify_only.read_text()), "receipt_mismatch"
        print("tree-path shore replay passed")
    elif args.output:
        atomic_write_json(args.output, result)
        print(result)
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
