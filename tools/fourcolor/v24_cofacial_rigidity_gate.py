#!/usr/bin/env python3
"""A failed two-cut explanation of cofacial colour rigidity.

The pentagonal prism refutes the broad implication: two nonincident
cofacial edges can be equal in every Tait colouring without forming a cut.
The optional stricter gate uses plantri's -m5 -c5 dual population, complete
independent colouring enumerators, and aggregate counts only. Neither this
stronger population nor its normal form is automatically preserved by a
reduction. No finite success here is a proof of an infinite implication.
"""

import argparse
import hashlib
from itertools import combinations
import json
from pathlib import Path
import subprocess

from v24_absolute_topology_gate import connected, enumerated
from v24_facial_bond_gate import validate
from v24_goldberg import edge_face_adjacency, make_goldberg_graph, consistently_oriented_face_cycles
from v24_plantri_seed_audit import graph_record, parse_ascii_graph


def prism():
    edges = sorted({tuple(sorted(e)) for i in range(5) for e in
                    ((i, (i + 1) % 5), (i + 5, (i + 1) % 5 + 5), (i, i + 5))})
    faces = [list(range(5)), list(range(5, 10))]
    faces += [[i, (i + 1) % 5, (i + 1) % 5 + 5, i + 5] for i in range(5)]
    return dict(primal_vertex_count=10, primal_edges=edges, face_cycles=faces)


def analyze(graph):
    validate(graph, 2)
    n, edges = graph['primal_vertex_count'], list(map(tuple, graph['primal_edges']))
    states = enumerated(n, edges)
    assert states, 'do not classify vacuous rigidity'
    faces = edge_face_adjacency(graph)
    tested, rigid = 0, []
    for i, j in combinations(range(len(edges)), 2):
        if set(edges[i]) & set(edges[j]) or not set(faces[i]) & set(faces[j]):
            continue
        tested += 1
        if all(c[i] == c[j] for c in states):
            rigid.append(dict(edges=[i, j], still_connected=connected(n,
                [e for k, e in enumerate(edges) if k not in (i, j)])))
    return dict(vertices=n, colorings=len(states), tested_pairs=tested, rigid=rigid)


def normal_form_loss():
    """Both planar smoothings of edge 01 in the spherical dodecahedron."""
    graph = make_goldberg_graph(1)
    validate(graph, 2)
    rho = {}
    for face in consistently_oriented_face_cycles(graph):
        for i, v in enumerate(face):
            rho[v, face[i - 1]] = face[(i + 1) % len(face)]
    rotation = []
    for v in range(20):
        a = min(w for u, w in rho if u == v)
        b = rho[v, a]
        rotation.append([a, b, rho[v, b]])
    records = []
    for pairs in (((2, 5), (4, 6)), ((2, 4), (5, 6))):
        mates = {a: b for u, v in pairs for a, b in ((u, v), (v, u))}
        smaller = [[mates[v] - 2 if w in (0, 1) else w - 2 for w in rotation[v]]
                   for v in range(2, 20)]
        reduced_graph = graph_record(smaller, 0)
        validate(reduced_graph, 2)
        records.append(dict(pairing=pairs, vertices=18,
                            face_lengths=sorted(map(len, reduced_graph['face_cycles']))))
    return records


def run(plantri=None, max_order=38):
    control = prism()
    row = analyze(control)
    assert row['colorings'] == 30
    assert any(r['still_connected'] for r in row['rigid'])
    result = dict(schema='fourcolor-cofacial-rigidity-gate-v1',
        control=dict(graph=control, analysis=row), population=[],
        normal_form_loss=normal_form_loss(),
        conclusion='broad two-cut implication false; stronger normal-form implication unproved')
    if plantri:
        result['generator_sha256'] = hashlib.sha256(plantri.read_bytes()).hexdigest()
        result['flags'] = ['-a', '-d', '-m5', '-c5']
        for n in range(20, max_order + 1, 2):
            output = subprocess.run([str(plantri), *result['flags'], str(n // 2 + 2)],
                                    capture_output=True, check=True).stdout
            # ASCII adjacency names extend above byte 127 at these orders.
            lines = [s for s in output.decode('latin1').split('\n') if s.strip()]
            aggregate = dict(vertices=n, graphs=len(lines), pairs=0, rigid_pairs=0,
                             colorings=0, embeddings_sha256=hashlib.sha256(output).hexdigest())
            for index, line in enumerate(lines):
                graph = graph_record(parse_ascii_graph(line), index)
                assert min(map(len, graph['face_cycles'])) >= 5
                row = analyze(graph)
                aggregate['pairs'] += row['tested_pairs']
                aggregate['rigid_pairs'] += len(row['rigid'])
                aggregate['colorings'] += row['colorings']
                if row['rigid']:
                    aggregate.setdefault('counterexamples', []).append(dict(graph=graph, analysis=row))
            result['population'].append(aggregate)
            print(json.dumps(aggregate, sort_keys=True), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plantri', type=Path)
    parser.add_argument('--max-order', type=int, default=38)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.plantri, args.max_order)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result['control']['analysis'], sort_keys=True))


if __name__ == '__main__':
    main()
