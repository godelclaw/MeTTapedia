#!/usr/bin/env python3
"""Test whether surviving-wire order suffices for a full cyclic matching.

The stronger proposed implication adds equal complete boundary sizes and
asks for a cyclic bijection fixing every surviving wire. Outcomes are a
finite geometric obstruction or no obstruction in the tested range; a
passing finite test would not establish the universal implication.
"""

import argparse
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_persistent_wire_order_gate import (
    connected, consistently_oriented_face_cycles, induced, prism,
    return_permutation, single_cycle, validate_sphere,
)


def audit():
    rows = []
    specimen = None
    for k in (5, 6):
        graph = prism(k)
        validate_sphere(graph)
        n, edges = graph["primal_vertex_count"], graph["primal_edges"]
        faces = consistently_oriented_face_cycles(graph)
        universe, sides = set(range(n)), []
        for mask in range(1 << n):
            side = {i for i in range(n) if mask >> i & 1}
            if not all(connected(n, edges, s) for s in (side, universe - side)):
                continue
            if any(sum(u in s and v in s for u, v in edges) < len(s)
                   for s in (side, universe - side)):
                continue
            cut = {i for i, (u, v) in enumerate(edges) if (u in side) != (v in side)}
            p = return_permutation(faces, side, cut, edges)
            q = return_permutation(faces, universe - side, cut, edges)
            assert single_cycle(p) and all(q[p[e]] == e for e in cut)
            sides.append((side, cut, p))
        checked, failures = 0, 0
        for A, ca, pa in sides:
            for B, cb, pb in sides:
                common = ca & cb
                if not A < B or len(ca) != len(cb) or len(common) < 2:
                    continue
                assert induced(pa, common) == induced(pb, common)
                checked += 1
                root = min(common)
                x = y = root
                forced = {}
                for _ in ca:
                    forced[x] = y
                    x, y = pa[x], pb[y]
                assert x == y == root and set(forced) == ca and set(forced.values()) == cb
                assert all(forced[pa[e]] == pb[forced[e]] for e in ca)
                if any(forced[e] != e for e in common):
                    failures += 1
                    if specimen is None:
                        specimen = dict(graph=graph, inner=sorted(A), outer=sorted(B),
                                        common=sorted(common), inner_order=sorted(pa.items()),
                                        outer_order=sorted(pb.items()),
                                        forced_matching=sorted(forced.items()))
        rows.append(dict(prism=k, same_width_pairs=checked, failures=failures))
    assert rows == [dict(prism=5, same_width_pairs=10, failures=0),
                    dict(prism=6, same_width_pairs=156, failures=24)]
    assert specimen is not None
    return json.loads(json.dumps(dict(schema="fourcolor-v24-persistent-wire-matching-v1",
                                    outcome="stronger_implication_refuted",
                                    cases=rows, specimen=specimen)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-only", type=Path)
    args = parser.parse_args()
    result = audit()
    if args.output:
        atomic_write_json(args.output, result)
    if args.verify_only:
        assert result == json.loads(args.verify_only.read_text()), "receipt_mismatch"
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
