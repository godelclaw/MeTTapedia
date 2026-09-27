#!/usr/bin/env python3
"""Replay a trapped Kempe class of an actual adjacent-pair deletion.

Unlike a closed smoothing, the retained graph has four degree-two ports.
Two independent complete searches enumerate its proper edge colourings.
An independent original-vertex component search checks the trapped class.
This is one proof-method counterexample, not a configuration catalogue.
The accompanying Lean theorem checks physical switch closure separately.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_absolute_topology_gate import girth
from v24_deletion_orbit_gate import colorings, vertex_colorings, orbits, incidence
from v24_facial_bond_gate import validate
from v24_geodesic_mincut_gate import connected
from v24_goldberg import edge_face_adjacency


def vertex_switches(n, edges, coloring):
    """Connected components of original vertices, independent of line-graph BFS."""
    for a, b in combinations(range(3), 2):
        active = [i for i, c in enumerate(coloring) if c in (a, b)]
        neighbors = [set() for _ in range(n)]
        for i in active:
            u, v = edges[i]
            neighbors[u].add(v)
            neighbors[v].add(u)
        todo = {v for v in range(n) if neighbors[v]}
        while todo:
            seen, stack = set(), [min(todo)]
            while stack:
                v = stack.pop()
                if v not in seen:
                    seen.add(v)
                    stack.extend(neighbors[v] - seen)
            todo -= seen
            changed = bytearray(coloring)
            for i in active:
                if edges[i][0] in seen:
                    assert edges[i][1] in seen
                    changed[i] = a + b - changed[i]
            yield bytes(changed)


def geometry(graph):
    """Literal connectivity and short dual-cycle diagnostics."""
    validate(graph, 2)
    n, edges = graph['primal_vertex_count'], graph['primal_edges']
    assert girth(n, edges) == 5
    assert all(connected(n, edges[:i] + edges[i + 1:], set(range(n)))
               for i in range(len(edges)))
    edge_faces = edge_face_adjacency(graph)
    nf = len(graph['face_cycles'])
    dual = [tuple(fs) for fs in edge_faces.values()]
    assert all(a != b for a, b in dual)
    assert len(set(tuple(sorted(e)) for e in dual)) == len(dual)
    deletion_checks = 0
    for k in range(5):
        for deleted in combinations(range(nf), k):
            assert connected(nf, dual, set(range(nf)) - set(deleted))
            deletion_checks += 1
    neighbors, edge_of = [set() for _ in range(nf)], {}
    for i, (u, v) in edge_faces.items():
        neighbors[u].add(v)
        neighbors[v].add(u)
        edge_of[frozenset((u, v))] = i
    counts = {}
    for length in (3, 4, 5):
        cuts = set()

        def visit(path):
            if len(path) == length:
                if path[0] in neighbors[path[-1]]:
                    cuts.add(tuple(sorted(edge_of[frozenset((u, v))]
                                          for u, v in zip(path, path[1:] + path[:1]))))
                return
            for v in neighbors[path[-1]]:
                if v > path[0] and v not in path:
                    visit(path + [v])

        for v in range(nf):
            visit([v])
        sizes = []
        for cut in sorted(cuts):
            adjacency = [set() for _ in range(n)]
            for i, (u, v) in enumerate(edges):
                if i not in cut:
                    adjacency[u].add(v)
                    adjacency[v].add(u)
            todo, shores = set(range(n)), []
            while todo:
                seen, stack = set(), [min(todo)]
                while stack:
                    v = stack.pop()
                    if v not in seen:
                        seen.add(v)
                        stack.extend(adjacency[v] - seen)
                todo -= seen
                shores.append(seen)
            assert len(shores) == 2
            cyclic = [sum(len(adjacency[v]) for v in side) // 2 >= len(side)
                      for side in shores]
            assert not all(cyclic) or (length == 5 and min(map(len, shores)) == 5)
            sizes.append(min(map(len, shores)))
        counts[str(length)] = dict(dual_cycles=len(cuts), small_shore_sizes=sorted(set(sizes)))
    return dict(girth=5, dual_deletion_checks=deletion_checks,
                dual_vertex_connectivity_at_least=5, short_dual_cycles=counts)


def normalized(c):
    names = {}
    return bytes(names.setdefault(x, len(names)) for x in c)


def run(source):
    graph = json.loads(source.read_text())['graph']
    geom = geometry(graph)
    n, edges = graph['primal_vertex_count'], list(map(tuple, graph['primal_edges']))
    removed = (0, 1)
    assert removed in edges
    retained_ids = [i for i, edge in enumerate(edges) if not set(edge) & set(removed)]
    retained = [edges[i] for i in retained_ids]
    full = colorings(n, edges)
    assert full == vertex_colorings(n, edges)
    states = colorings(n, retained)
    assert states == vertex_colorings(n, retained)
    inc = incidence(n, retained)
    ports = [[w for e in edges if z in e for w in e if w not in removed] for z in removed]
    assert ports == [[2, 3], [4, 5]]
    assert all(len(inc[v]) == 2 for v in ports[0] + ports[1])

    def requests(c):
        return [next(iter(set(range(3)) - {c[i] for i in inc[v]}))
                for v in ports[0] + ports[1]]

    def accepted(c):
        q = requests(c)
        return q[0] != q[1] and q[2] != q[3] and set(q[:2]) == set(q[2:])

    projected = {bytes(c[i] for i in retained_ids) for c in full}
    assert projected == {c for c in states if accepted(c)}
    obs = orbits(n, retained, states)
    counts = [len(set(orbit) & projected) for orbit in obs]
    bad = obs[counts.index(0)]
    seen, stack = set(), [bad[0]]
    while stack:
        c = stack.pop()
        if c not in seen:
            seen.add(c)
            stack.extend(set(vertex_switches(n, retained, c)) - seen)
    assert seen == set(bad)
    assert all(requests(c)[0] == requests(c)[1] for c in bad)
    representatives = sorted({normalized(c) for c in bad})
    assert (len(full), len(states), list(map(len, obs)), counts, len(representatives)) == (
        96, 288, [36, 36, 216], [24, 0, 72], 6)
    return dict(schema='open-adjacent-pair-orbit-v1', graph=graph, geometry=geom,
                removed_vertices=list(removed), retained_edge_ids=retained_ids, ports=ports,
                full_colorings=len(full), retained_colorings=len(states),
                orbit_sizes=list(map(len, obs)), extending_in_orbits=counts,
                trapped_representatives=[list(c) for c in representatives],
                trapped_seed=list(bad[0]), full_coloring=list(full[0]),
                scope='All finite Kempe histories in one deleted-graph class fail to extend; '
                      'other retained classes do extend. Small-cut tests are diagnostics, '
                      'not premises of the Lean switch-closure theorem.')


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path,
                        default=root / 'results/fourcolor/v24_smoothing_provenance_gate.json')
    parser.add_argument('--output', type=Path,
                        default=root / 'results/fourcolor/v24_open_pair_orbit_gate.json')
    args = parser.parse_args()
    result = run(args.source)
    atomic_write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('full_colorings', 'retained_colorings',
                                            'orbit_sizes', 'extending_in_orbits', 'geometry')}))
