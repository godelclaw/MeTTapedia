#!/usr/bin/env python3
"""Gate the actual-path-to-Count-node connection, without enumerating colours.

Prediction: a connected cubic side with at least as many vertices as its
full cut edges contains a cycle. Hence a canonical path split with each
terminal block at least the width has cycles on both sides. Its incident
edge shore must have connected complement, nonempty majority regions, and
middle width at most the full cut size. Small endpoint blocks are negative
controls: connected optimal bonds alone need not contain two cycles.
"""
import argparse
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_buffered_shell_gate import contours
from v24_geodesic_mincut_gate import minimum_cut, verify_certificate, connected
from v24_goldberg import make_goldberg_graph
from v24_unsplit_cap_sweep_gate import graph as ring_graph


def has_cycle(n, edges, side):
    assert connected(n, edges, side)
    return sum(u in side and v in side for u, v in edges) >= len(side)


def check_node(n, edges, side):
    other = set(range(n)) - side
    assert has_cycle(n, edges, side) and has_cycle(n, edges, other)
    shore = {i for i, (u, v) in enumerate(edges) if u in side or v in side}
    counts = [sum(i in shore and v in e for i, e in enumerate(edges)) for v in range(n)]
    assert any(x >= 2 for x in counts) and any(x <= 1 for x in counts)
    middle = sum(0 < x < 3 for x in counts)
    width = sum((u in side) != (v in side) for u, v in edges)
    assert middle <= width
    for selected in (shore, set(range(len(edges))) - shore):
        selected_edges = [e for i, e in enumerate(edges) if i in selected]
        vertices = {v for e in selected_edges for v in e}
        assert connected(n, selected_edges, vertices)
    return shore, middle


def run():
    cube = [(v, v ^ (1 << b)) for v in range(8) for b in range(3) if v < (v ^ (1 << b))]
    connected_sides = cycles = trees = 0
    for mask in range(1, 255):
        s = {v for v in range(8) if mask >> v & 1}
        if not connected(8, cube, s):
            continue
        connected_sides += 1
        width = sum((u in s) != (v in s) for u, v in cube)
        if has_cycle(8, cube, s):
            cycles += 1
        else:
            trees += 1
            assert len(s) + 2 == width
        if width <= len(s):
            assert has_cycle(8, cube, s)
    # An optimal connected bond of width three need not have two cyclic sides.
    endpoint_path = [0, 1, 3, 7]
    assert all(tuple(sorted((a, b))) in cube for a, b in zip(endpoint_path, endpoint_path[1:]))
    s, paths = minimum_cut(8, cube, {0}, set(endpoint_path[1:]))
    cut = verify_certificate(8, cube, {0}, set(endpoint_path[1:]), s, paths)
    assert s == {0} and len(cut) == 3 and not has_cycle(8, cube, s)
    rows = []
    samples = []
    for n in (3, 5, 8, 12):
        samples.append((f'ring-{n}', ring_graph(n), [v for i in range(n) for v in (n+i, 2*n+i)]))
    for k in range(1, 5):
        g = make_goldberg_graph(k)
        _, cs = contours(g, 0)
        samples.append((f'GP-{k}', g, cs[len(cs)//2]['cycle']))
    for name, g, path in samples:
        n, edges = g['primal_vertex_count'], g['primal_edges']
        assert all(sum(v in e for e in edges) == 3 for v in range(n))
        eligible, cyclic, previous, widths = [], [], None, []
        for t in range(1, len(path)):
            a, b = set(path[:t]), set(path[t:])
            s, packing = minimum_cut(n, edges, a, b)
            cut = verify_certificate(n, edges, a, b, s, packing)
            w = len(cut)
            widths.append(w)
            if w <= min(len(a), len(b)):
                assert has_cycle(n, edges, s) and has_cycle(n, edges, set(range(n))-s)
                eligible.append(t)
            if has_cycle(n, edges, s) and has_cycle(n, edges, set(range(n))-s):
                shore, middle = check_node(n, edges, s)
                if previous is not None:
                    assert previous < shore
                previous = shore
                cyclic.append(dict(t=t, full_width=w, middle_width=middle))
        rows.append(dict(name=name, path_vertices=len(path), widths=widths,
                         terminal_guaranteed=eligible, actual_cyclic=cyclic))
    return dict(schema='fourcolor-v24-path-count-v1', cube=dict(connected_sides=connected_sides,
                cyclic_sides=cycles, tree_sides=trees),
                endpoint_counterexample=dict(path=endpoint_path, side=[0], width=3),
                sweeps=rows, scope='geometry and node fields only; no colour enumeration or universal width claim')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    if args.output:
        atomic_write_json(args.output, result)
    print(json.dumps(result))
