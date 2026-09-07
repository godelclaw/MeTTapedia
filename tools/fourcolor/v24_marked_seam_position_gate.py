#!/usr/bin/env python3
"""Calibrate full cyclic seam matching with explicit marked-wire positions.

The criterion tested before formalization is equality of normalized full
boundary rotation and of each named wire's optional coordinate.  Expected
outcome: it characterizes the coordinate-induced matching fixing the marks;
the previous 24 prism failures must be rejected when all common wires are
marked.  Empty, singleton and multiple marked sets, absent labels and every
relative cyclic root are tested.  These are geometry controls, not colouring
or configuration certificates.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_persistent_wire_order_gate import (
    connected, consistently_oriented_face_cycles, induced, prism,
    return_permutation, single_cycle, validate_sphere,
)


def coordinates(successor, root):
    result, point = {}, root
    for i in range(len(successor)):
        result[point] = i
        point = successor[point]
    assert point == root and len(result) == len(successor)
    return result


def audit():
    rows = []
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
            assert single_cycle(p)
            sides.append((side, cut, p))
        pairs = rejected = checks = accepted = absent = 0
        mark_sizes = set()
        for A, ca, pa in sides:
            for B, cb, pb in sides:
                common = sorted(ca & cb)
                if not A < B or len(ca) != len(cb) or len(common) < 2:
                    continue
                pairs += 1
                assert induced(pa, set(common)) == induced(pb, set(common))
                ci = coordinates(pa, common[0])
                any_full = False
                for root in cb:
                    co = coordinates(pb, root)
                    inv = {v: e for e, v in ci.items()}
                    matching = {e: inv[co[e]] for e in cb}
                    assert all(matching[pb[e]] == pa[matching[e]] for e in cb)
                    full = all(ci[e] == co[e] for e in common)
                    any_full |= full
                    for size in range(len(common) + 1):
                        for marks in itertools.combinations(common, size):
                            # Include a label absent from both boundaries.
                            labels = marks + (len(edges),)
                            same = all(ci.get(e) == co.get(e) for e in labels)
                            fixed = all(matching[e] == e for e in marks)
                            assert same == fixed
                            mark_sizes.add(size)
                            checks += 1
                            accepted += same
                            absent += 1
                    # Presence is part of the record, not only position.
                    for e in ca ^ cb:
                        assert ci.get(e) != co.get(e)
                rejected += not any_full
        assert (pairs, rejected) == ((10, 0) if k == 5 else (156, 24))
        assert {0, 1, 2} <= mark_sizes and accepted > 0 and absent == checks
        rows.append(dict(prism=k, pairs=pairs, no_full_wire_matching=rejected,
                         coordinate_tests=checks, accepted=accepted,
                         absent_label_tests=absent, marked_sizes=sorted(mark_sizes)))
    return dict(schema="fourcolor-v24-marked-seam-position-v1",
                outcome="position_criterion_passes_controls", cases=rows)


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
