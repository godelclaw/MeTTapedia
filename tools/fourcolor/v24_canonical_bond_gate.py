#!/usr/bin/env python3
"""Test optimal full cuts with connected terminals and movable caps.

Prediction: every minimum edge cut between nonempty connected terminal
sets in a connected graph has two connected shores. The canonical minima
nest as terminals advance. Width is measured, not assumed bounded.
Negative controls drop terminal or ambient connectedness. No colourings
or configuration certificates are enumerated.
"""
import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_buffered_shell_gate import contours
from v24_geodesic_mincut_gate import (
    boundary_order, connected, minimum_cut, validate_sphere, verify_certificate,
)
from v24_goldberg import edge_face_adjacency, make_goldberg_graph
from v24_unsplit_cap_sweep_gate import graph as ring_graph


def brute(n, edges, source, sink):
    candidates = []
    for mask in range(1 << n):
        side = {v for v in range(n) if mask >> v & 1}
        if source <= side and not side & sink:
            width = sum((u in side) != (v in side) for u, v in edges)
            candidates.append((width, len(side), mask))
    best = min(candidates)
    minima = [{v for v in range(n) if mask >> v & 1}
              for w, _, mask in candidates if w == best[0]]
    return best, minima


def finite_gate():
    samples = [(4, list(itertools.combinations(range(4), 2))),
               (6, [(i, (i + 1) % 6) for i in range(6)]),
               (8, [(v, v ^ (1 << b)) for v in range(8) for b in range(3)
                    if v < (v ^ (1 << b))])]
    pairs = optimal = 0
    for n, edges in samples:
        whole = set(range(n))
        assert connected(n, edges, whole)
        for labels in itertools.product(range(3), repeat=n):
            a = {v for v, x in enumerate(labels) if x == 1}
            b = {v for v, x in enumerate(labels) if x == 2}
            if not (connected(n, edges, a) and connected(n, edges, b)):
                continue
            best, minima = brute(n, edges, a, b)
            assert all(connected(n, edges, s) and connected(n, edges, whole - s)
                       for s in minima)
            side, paths = minimum_cut(n, edges, a, b)
            verify_certificate(n, edges, a, b, side, paths)
            assert sum(1 << v for v in side) == best[2]
            pairs += 1
            optimal += len(minima)
    # Missing connectedness really invalidates the conclusion.
    best, _ = brute(5, [(i, i + 1) for i in range(4)], {0, 4}, {2})
    assert best == (2, 2, 17)  # disconnected source shore
    best, _ = brute(4, [(0, 1), (2, 3)], {0}, {1})
    assert best == (1, 1, 1)  # complementary shore includes a floating component
    return dict(terminal_pairs=pairs, all_optimal_sides=optimal,
                negative_controls=2)


def sweep(g, cycle):
    validate_sphere(g)
    n, edges = g['primal_vertex_count'], g['primal_edges']
    edge_faces = edge_face_adjacency(g)
    previous, widths, witnesses = None, [], []
    for t in range(1, len(cycle)):
        a, b = set(cycle[:t]), set(cycle[t:])
        side, paths = minimum_cut(n, edges, a, b)
        cut = verify_certificate(n, edges, a, b, side, paths)
        order, faces = boundary_order(edge_faces, cut)
        if previous is not None:
            assert previous < side
        previous = side
        widths.append(len(cut))
        witnesses.append(dict(t=t, side=sorted(side), paths=paths,
                              cut_order=order, face_order=faces))
    # Retain a packing/cut certificate for the largest optimum. Re-running
    # checks every intermediate cut, not only this exported witness.
    worst = max(range(len(widths)), key=widths.__getitem__)
    return dict(vertices=n, cycle=cycle, widths=widths,
                maximum_witness=witnesses[worst])


def run():
    small = finite_gate()
    rings = []
    for n in (3, 5, 8, 12):
        r = sweep(ring_graph(n), [v for i in range(n) for v in (n+i, 2*n+i)])
        assert max(r['widths']) <= 6
        rings.append(r)
    spheres = []
    for k in range(1, 5):
        g = make_goldberg_graph(k)
        _, rows = contours(g, 0)
        cycle = rows[len(rows)//2]['cycle']
        spheres.append(sweep(g, cycle))
    return dict(schema='fourcolor-v24-canonical-bond-v1', finite=small,
                rings=rings, spheres=spheres,
                scope='minimum full interfaces; no universal width or shortening claim')


def verify_maximum(g, row):
    """Replay the exported cut/packing lower and upper bounds independently."""
    validate_sphere(g)
    n, edges = g['primal_vertex_count'], g['primal_edges']
    assert row['vertices'] == n
    witness, cycle = row['maximum_witness'], row['cycle']
    t = witness['t']
    assert 0 < t < len(cycle)
    cut = verify_certificate(n, edges, set(cycle[:t]), set(cycle[t:]),
                             set(witness['side']), witness['paths'])
    order, faces = boundary_order(edge_face_adjacency(g), cut)
    assert witness['cut_order'] == order and witness['face_order'] == faces
    assert len(cut) == max(row['widths']) == row['widths'][t-1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    if args.output:
        atomic_write_json(args.output, result)
    print(json.dumps(dict(finite=result['finite'],
                         ring_maxima=[max(r['widths']) for r in result['rings']],
                         sphere_maxima=[max(r['widths']) for r in result['spheres']])))


if __name__ == '__main__':
    main()
