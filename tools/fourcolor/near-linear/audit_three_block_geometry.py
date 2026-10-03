#!/usr/bin/env python3
"""Check the hypotheses and separator on the retained D0092 sphere.

Lean proves the parameterized geometric and reconstruction laws. This
independent program instantiates their geometric data on the retained
example; it is not a kernel certificate for that sphere's rotation system.
"""
from collections import Counter, deque
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_clique_fill import source_faces
from audit_component_detach import data
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_three_block_core import path
from audit_two_port_core import eliminate
from probe_flat_pairs import geometry

TRIANGLES = [(2,3,15), (3,12,15), (11,15,12), (11,12,14),
             (12,13,14), (7,14,13), (5,13,12)]
RETURN = [1,15,12,13,6]


def verify(here):
    fixture, ambient, exterior, ports, initial, *_ = data(here)
    raw = (here / fixture['configuration']).read_bytes()
    ring, source = graph(raw)
    image = fixture['images']
    require(len(image) == len(set(image)) == 18, 'Source reading not injective')
    require(all(image[v] in ambient[image[u]] for u, ns in enumerate(source) for v in ns),
            'Missing source edge')
    require(all({image[v] for v in source[u]} == ambient[image[u]]
                for u in range(ring, len(source))), 'Incomplete source core star')
    require(set(exterior) == set(ambient) - set(image[ring:]), 'Exterior coverage changed')
    faces = [tuple(reversed(t)) for t in fixture['faces']]
    darts, _, _, _ = geometry(faces)
    require(len(ambient) - len(darts)//2 + len(faces) == 2, 'Wrong Euler characteristic')
    source_triangles = set(source_faces(raw))
    for a,b,c in TRIANGLES:
        require((a,b,c) in source_triangles, 'Not an oriented source face')
        u,v,w = (image[i] for i in (a,b,c))
        require(darts[u,v][1] == w and darts[v,w][1] == u and darts[w,u][1] == v,
                'Source triangle rotation not preserved')

    prepared, _ = switch(exterior, initial, (1,2), 133)
    coloured, pivot = switch(exterior, prepared, (0,1), 43)
    require(pivot == {43}, 'Wrong pivot')
    p = path(exterior, coloured, (1,3), ports[1], ports[6])
    require(p is not None, 'Complementary path absent')
    require(path(exterior, prepared, (1,3), ports[1], ports[6]) is None,
            'Path already present before pivot')
    closed = [image[i] for i in RETURN] + list(reversed(p))[1:]
    require(closed[0] == closed[-1], 'Walk not closed')
    require(all(v in ambient[u] for u,v in zip(closed,closed[1:])), 'Missing walk edge')
    parity = Counter(tuple(sorted(e)) for e in zip(closed,closed[1:]))
    labels, todo = {0: 0}, deque([0])
    dual = {i: [] for i in range(len(faces))}
    for (u,v),(i,_) in darts.items():
        dual[i].append((darts[v,u][0], parity[tuple(sorted((u,v)))] % 2))
    while todo:
        i = todo.popleft()
        for j, flip in dual[i]:
            wanted = labels[i] ^ flip
            if j in labels:
                require(labels[j] == wanted, 'Inconsistent face potential')
            else:
                labels[j] = wanted
                todo.append(j)
    require(len(labels) == len(faces), 'Dual disconnected')
    endpoint_sides = [labels[darts[image[a],image[b]][0]] for a,b in [(2,3),(5,13),(7,14)]]
    require(endpoint_sides[0] == endpoint_sides[1] != endpoint_sides[2],
            'Wrong source-side separation')
    require(all(path(exterior, coloured, (0,2), ports[i], ports[7]) is None for i in (2,5)),
            'Complementary paths cross')
    final, component = switch(exterior, coloured, (0,2), ports[7])
    require([i for i,v in enumerate(ports) if v in component] == [7,8,9,10],
            'Switch changes wrong boundary run')
    witness, _ = eliminate(source, ring, [final[v] for v in ports])
    require(witness is not None, 'Source fails to reconstruct')
    proper(ambient, final | {image[v]: c for v,c in witness.items()})
    return {
        'evidence': 'Program instantiation of the separate parameterized Lean path-separation and whole-reconstruction laws.',
        'fixture_sha256': sha256((here / 'component-detach-example.json').read_bytes()).hexdigest(),
        'source_sha256': sha256(raw).hexdigest(),
        'ambient_vertices': len(ambient), 'exterior_vertices': len(exterior),
        'edges': len(darts)//2, 'faces': len(faces),
        'source_core_vertices': 7, 'source_triangles_used': TRIANGLES,
        'source_return_path': RETURN, 'exterior_complementary_path_edges': len(p)-1,
        'closed_walk_edges': len(closed)-1, 'face_labels_at_ports_2_5_7': endpoint_sides,
        'switched_component_vertices': len(component), 'changed_ports': [7,8,9,10],
        'whole_colouring_checked': True, 'new_graph_fixture_bytes': 0,
        'scope': 'One geometric input replay. The Lean theorem allows arbitrary exterior size, subject to its sphere, source, boundary-word and complementary-path hypotheses. Useful-path supply is open.'}


if __name__ == '__main__':
    here = Path(__file__).resolve().parent
    print(json.dumps(verify(here), indent=2))
