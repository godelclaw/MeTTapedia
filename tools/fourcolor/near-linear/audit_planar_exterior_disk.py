#!/usr/bin/env python3
"""Check the retained punctured rotation against the planar disk contract.

This is a geometric program diagnostic, not a Lean planarity certificate.
The generic disk-to-Kempe-closure theorem is checked separately in Lean.
No colouring search or new repair data is generated.
"""
import argparse
import ast
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_diamond_sources import require
from probe_flat_pairs import geometry


def verify(here):
    path = here / 'component-detach-example.json'
    fixture = json.loads(path.read_text())
    for name, expected in ((fixture['source_fixture'], fixture['source_fixture_sha256']),
                           (fixture['configuration'], fixture['configuration_sha256'])):
        require(sha256((here / name).read_bytes()).hexdigest() == expected, 'Source pin differs')
    _, ambient, nexts, _ = geometry(fixture['faces'])
    ports, deleted = fixture['images'][:11], set(fixture['images'][11:])
    require(len(deleted) == 7 and len(set(ports)) == 11, 'Source carrier differs')
    exterior = {v: ns - deleted for v, ns in ambient.items() if v not in deleted}
    require(all(exterior.values()), 'An isolated exterior vertex has no dart')
    rho = {}
    for v, neighbours in exterior.items():
        for u in neighbours:
            w = nexts[v, u]
            for _ in range(len(ambient[v])):
                if w not in deleted:
                    break
                w = nexts[v, w]
            require(w in neighbours, 'Restricted vertex rotation does not return')
            rho[v, u] = (v, w)
    require(set(rho.values()) == set(rho), 'Restricted rotation is not a permutation')
    for v, neighbours in exterior.items():
        start = (v, min(neighbours))
        d, seen = start, set()
        while d not in seen:
            seen.add(d)
            d = rho[d]
        require(d == start and {u for _, u in seen} == neighbours,
                'More than one rotation cycle at a vertex')
    phi = {d: rho[d[1], d[0]] for d in rho}
    faces, unseen = [], set(phi)
    while unseen:
        start, face = min(unseen), []
        d = start
        while d in unseen:
            unseen.remove(d)
            face.append(d)
            d = phi[d]
        require(d == start, 'Facial walk did not close at its first dart')
        faces.append(face)
    boundary = list(zip(ports, ports[1:] + ports[:1]))
    require(all(phi[a] == b for a, b in zip(boundary, boundary[1:] + boundary[:1])),
            'The facial boundary is not in the source port order')
    outside = [f for f in faces if set(f) != set(boundary)]
    require(len(outside) + 1 == len(faces) and all(len(f) == 3 for f in outside),
            'Another nontriangular face remains')
    seen, todo = {min(exterior)}, [min(exterior)]
    while todo:
        for v in exterior[todo.pop()]:
            if v not in seen:
                seen.add(v)
                todo.append(v)
    require(seen == set(exterior), 'The exterior is disconnected')
    nv, ne, nf = len(exterior), len(rho) // 2, len(faces)
    require(nv - ne + nf == 2, 'The induced rotation has positive genus')

    # Match exactly the vertex graph consumed by the existing Lean examples.
    carrier = sorted(exterior)
    label = {v: i for i, v in enumerate(carrier)}
    edges = sorted((label[u], label[v]) for u, ns in exterior.items() for v in ns if u < v)
    lean_path = (here.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor'
                 / 'ComponentDetachExample.lean')
    text = lean_path.read_text()
    for name, expected in [('edges', edges), ('carrier', carrier),
                           ('ports', [label[v] for v in ports])]:
        match = re.search(rf'^def {name} :[^\n]*:= (\[[^\n]*\])$', text, re.M)
        require(match is not None and ast.literal_eval(match[1]) == expected,
                f'Lean {name} differs from the punctured input')
    return {
        'classification': 'PROGRAM_CHECKED_EXTERIOR_DISK_GEOMETRY',
        'fixture': path.name, 'fixture_sha256': sha256(path.read_bytes()).hexdigest(),
        'vertices_removed': len(deleted), 'vertices': nv, 'edges': ne,
        'darts': len(rho), 'faces': nf,
        'face_lengths': dict(sorted(Counter(map(len, faces)).items())),
        'euler_characteristic': nv - ne + nf,
        'connected': True, 'one_rotation_cycle_per_vertex': True,
        'ordered_boundary': ports,
        'lean_graph_and_order_match': True,
        'lean_geometry_certified': False,
        'scope': 'One retained exterior. Uniform patch-deletion geometry is not proved.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(report)
    else:
        print(report, end='')
