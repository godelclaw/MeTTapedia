#!/usr/bin/env python3
"""A cofacial cycle-lift fails even after unrestricted recolouring.

Replay one closed-graph counterexample, not a boundary-word catalogue.
Two independent complete colouring searches and an independent perfect-
matching search test the same common-cycle claim. Inverse insertion is
constructed as an actual spherical rotation and is colourable. Hence this
refutes the proposed cycle-based lift, not arbitrary colouring lifts.
Neither graph is a least counterexample or in the girth-five normal form.
"""
import argparse
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path

from v24_absolute_topology_gate import enumerated, girth
from v24_annular_census import atomic_write_json
from v24_deletion_orbit_gate import PAIRS, components, incidence, orbits
from v24_facial_bond_gate import validate
from v24_geodesic_mincut_gate import connected
from v24_goldberg import edge_face_adjacency, make_goldberg_graph
from v24_plantri_seed_audit import graph_record, parse_ascii_graph


ASCII = '18 bcd,aef,agh,aij,bkl,bmg,cfn,coi,dhj,dip,eql,ekm,flr,gro,hnp,joq,kpr,mqn'
MARKS = (8, 9)


def common_cycles(n, edges, coloring, marks):
    inc = incidence(n, edges)
    return [(pair, part) for pair in PAIRS
            for part in components(inc, coloring, pair)
            if set(marks) <= set(part)]


def perfect_matchings(n, edges):
    inc = incidence(n, edges)

    def visit(unmatched):
        if not unmatched:
            yield frozenset()
            return
        v = min(unmatched)
        for e in inc[v]:
            if set(edges[e]) <= unmatched:
                for matching in visit(unmatched - set(edges[e])):
                    yield matching | {e}

    return list(visit(set(range(n))))


def complement_cycles(n, edges, matching):
    """Trace the degree-two complement directly; no colour search is used."""
    inc = incidence(n, edges)
    todo = set(range(len(edges))) - matching
    assert all(len(set(row) & todo) == 2 for row in inc)
    result = []
    while todo:
        first = min(todo)
        v, start = edges[first]
        part = [first]
        todo.remove(first)
        while v != start:
            nxt = set(inc[v]) & todo
            assert len(nxt) == 1
            e = nxt.pop()
            todo.remove(e)
            part.append(e)
            v = next(w for w in edges[e] if w != v)
        result.append(sorted(part))
    return result


def check_geometry(graph):
    validate(graph, 2)
    n, edges = graph['primal_vertex_count'], graph['primal_edges']
    vertices = set(range(n))
    assert all(connected(n, edges[:e] + edges[e + 1:], vertices)
               for e in range(len(edges))), 'bridge'
    assert all(connected(n, edges, vertices - set(xs))
               for k in (1, 2) for xs in combinations(range(n), k)), 'not three-connected'


def inverse_insertion(rotation, graph, marks):
    """Subdivide the designated edges and join their new vertices.

    Preserve all old cyclic orders. Of the four choices at the new
    vertices, retain the one with spherical Euler characteristic.
    """
    n = graph['primal_vertex_count']
    (a, b), (c, d) = [graph['primal_edges'][i] for i in marks]
    assert len({a, b, c, d}) == 4
    assert set(edge_face_adjacency(graph)[marks[0]]) & set(edge_face_adjacency(graph)[marks[1]])
    candidates = []
    for flip_left, flip_right in product((False, True), repeat=2):
        rows = [row[:] for row in rotation] + [[a, b, n + 1], [c, d, n]]
        if flip_left:
            rows[n].reverse()
        if flip_right:
            rows[n + 1].reverse()
        for u, v, new in ((a, b, n), (b, a, n), (c, d, n + 1), (d, c, n + 1)):
            rows[u][rows[u].index(v)] = new
        try:
            expanded = graph_record(rows, 0)
        except AssertionError:
            continue
        check_geometry(expanded)
        candidates.append(expanded)
    assert len(candidates) == 1
    expanded = candidates[0]
    # Check the exact inverse on original vertex labels, not just counts.
    old = {tuple(e) for e in graph['primal_edges']}
    retained = {tuple(e) for e in expanded['primal_edges'] if max(e) < n}
    assert retained | {tuple(graph['primal_edges'][i]) for i in marks} == old
    assert len(expanded['primal_edges']) == len(old) + 3
    return expanded


def run():
    rotation = parse_ascii_graph(ASCII)
    graph = graph_record(rotation, 0)
    check_geometry(graph)
    n, edges = graph['primal_vertex_count'], graph['primal_edges']
    faces = edge_face_adjacency(graph)
    shared = sorted(set(faces[8]) & set(faces[9]))
    assert shared == [2] and len(graph['face_cycles'][2]) == 8
    states = enumerated(n, edges)
    assert len(states) == 36
    assert all(not common_cycles(n, edges, c, MARKS) for c in states)
    orbit_sizes = sorted(map(len, orbits(n, edges, states)))
    assert orbit_sizes == [36]
    projections = Counter(tuple(c[i] for i in MARKS) for c in states)
    assert projections == Counter({w: 4 for w in product(range(3), repeat=2)})
    matchings = perfect_matchings(n, edges)
    assert len(matchings) == len(set(matchings)) == 23
    factors = [complement_cycles(n, edges, m) for m in matchings]
    even = [f for f in factors if all(len(c) % 2 == 0 for c in f)]
    assert len(even) == 13
    assert not any(set(MARKS) <= set(c) for f in even for c in f)
    assert sum(3 * 2 ** len(f) for f in even) == 3 * len(states)
    expanded = inverse_insertion(rotation, graph, MARKS)
    upstairs = enumerated(20, expanded['primal_edges'])
    assert len(upstairs) == 72
    control = make_goldberg_graph(1)
    validate(control, 2)
    control_states = enumerated(20, control['primal_edges'])
    assert len(control_states) == 60
    control_faces = edge_face_adjacency(control)
    control_pairs = [p for p in combinations(range(30), 2)
                     if not set(control['primal_edges'][p[0]]) & set(control['primal_edges'][p[1]])
                     and set(control_faces[p[0]]) & set(control_faces[p[1]])]
    assert all(common_cycles(20, control['primal_edges'], c, p)
               for c in control_states for p in control_pairs)
    return dict(schema='fourcolor-v24-smoothing-cycle-v1', graph=graph,
        marks=list(MARKS), shared_faces=shared, colorings=len(states), orbit_sizes=orbit_sizes,
        marked_patterns=len(projections), colorings_per_pattern=4,
        perfect_matchings=len(matchings), even_factors=len(even),
        factor_lengths={','.join(map(str, ls)): count for ls, count in sorted(Counter(
            tuple(sorted(map(len, f))) for f in even).items())},
        common_cycle_colorings=0, inverse=expanded, inverse_colorings=len(upstairs),
        inverse_witness=list(upstairs[0]), girth=girth(n, edges),
        inverse_girth=girth(20, expanded['primal_edges']),
        positive_control=dict(vertices=20, colorings=60, cofacial_pairs=len(control_pairs)),
        scope='closed generic cycle-lift refutation; neither girth-five normal-form nor zero-Count obstruction')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    if args.output:
        atomic_write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('colorings', 'perfect_matchings', 'even_factors',
        'common_cycle_colorings', 'inverse_colorings', 'girth', 'inverse_girth')}, sort_keys=True))


if __name__ == '__main__':
    main()
