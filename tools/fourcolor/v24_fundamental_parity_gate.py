#!/usr/bin/env python3
"""Generic original-edge parity regression, including parallel endpoint pairs.

Enumerate labelled trees on one through five vertices and every choice of
root. Add each possible extra edge with its own identity, even when its
endpoint pair already occurs in the tree. Check root-path boundaries,
uniqueness from parity plus nonforest support, and the fundamental support
and its root-distance bound. This enumerates no Tait or ring colourings.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json


def root_tree(n, edges, root):
    adj = [[] for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        adj[u].append((v, e))
        adj[v].append((u, e))
    paths, depth, order = {root: 0}, {root: 0}, [root]
    for u in order:
        for v, e in adj[u]:
            if v not in paths:
                paths[v] = paths[u] ^ (1 << e)
                depth[v] = depth[u] + 1
                order.append(v)
    return paths, depth


def boundary(mask, endpoints):
    result = 0
    for e, (u, v) in enumerate(endpoints):
        if mask & (1 << e):
            result ^= (1 << u) ^ (1 << v)
    return result


def run():
    rows = []
    expected_trees = [1, 1, 3, 16, 125]
    for n in range(1, 6):
        pairs = list(itertools.combinations(range(n), 2))
        trees = root_checks = fundamental_checks = parallel_checks = subset_checks = 0
        for edges in itertools.combinations(pairs, n - 1):
            if len(root_tree(n, edges, 0)[0]) != n:
                continue
            trees += 1
            for root in range(n):
                paths, depth = root_tree(n, edges, root)
                for v in range(n):
                    assert boundary(paths[v], edges) == (1 << v) ^ (1 << root), "root_boundary_failure"
                    assert paths[v].bit_count() == depth[v], "root_length_failure"
                    root_checks += 1
                for extra in pairs:
                    all_edges = edges + (extra,)
                    extra_bit = 1 << len(edges)
                    u, v = extra
                    cycle = paths[u] ^ paths[v] ^ extra_bit
                    assert cycle & extra_bit and boundary(cycle, all_edges) == 0, "cycle_failure"
                    assert cycle.bit_count() <= depth[u] + depth[v] + 1, "width_failure"
                    seen = {}
                    even_with_extra = []
                    for mask in range(1 << len(all_edges)):
                        parity = boundary(mask, all_edges)
                        key = (mask & extra_bit, parity)
                        assert key not in seen, "uniqueness_failure"
                        seen[key] = mask
                        if mask & extra_bit and parity == 0:
                            even_with_extra.append(mask)
                        subset_checks += 1
                    assert even_with_extra == [cycle], "full_support_failure"
                    fundamental_checks += 1
                    parallel_checks += int(extra in edges)
        assert trees == expected_trees[n - 1], "tree_calibration_failure"
        rows.append(dict(vertices=n, trees=trees, root_checks=root_checks,
                         fundamental_checks=fundamental_checks, parallel_checks=parallel_checks,
                         subset_checks=subset_checks))
    return dict(schema="fourcolor-v24-fundamental-parity-v1", outcome="passed", rows=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    if args.verify_only:
        assert result == json.loads(args.verify_only.read_text()), "receipt_mismatch"
        print("original-edge fundamental parity replay passed")
    elif args.output:
        atomic_write_json(args.output, result)
        print(result)
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
