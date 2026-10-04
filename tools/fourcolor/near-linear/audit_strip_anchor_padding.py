#!/usr/bin/env python3
"""Replay the minimum-degree-five anchor trap without a new repair search.

Lean transports the obstruction along the retained graph homomorphism.
This independent check reconstructs the spherical face complex, exact core
occurrence, physical switches, separating seams and literal Lean data.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_anchor_trap import definition, direct_solver
from audit_strip_phase import geometry


def verify(here):
    path = here / 'strip-anchor-padding-example.json'
    f = json.loads(path.read_text())
    base = json.loads((here / f['base_fixture']).read_text())
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() == f['source_sha256'] == base['source_sha256'],
            'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source carriers differ')
    old = geometry(base['faces'], list(range(ring)))
    exterior = geometry(f['faces'], list(range(ring)))
    n = len(exterior)
    require(n == 48, 'Exterior carrier differs')
    require(all(old[v] <= exterior[v] for v in old), 'Old edge missing')
    source_vertex = lambda v: v if v < ring else n + v - ring
    triangles = [list(t) for t in combinations(range(19), 3)
                 if all(v in source[u] for u, v in combinations(t, 2))]
    faces = f['faces'] + [[source_vertex(v) for v in t] for t in triangles]
    require(faces == f['whole_faces'], 'Glued faces differ')
    whole = geometry(faces, [])
    require(len(whole) == 56 and min(map(len, whole.values())) == 5,
            'Minimum-degree-five sphere differs')
    for v in range(n):
        require(whole[v] & set(range(n)) == exterior[v], 'Exterior is not induced')
    for v in range(ring, len(source)):
        require(whole[source_vertex(v)] == {source_vertex(w) for w in source[v]},
                'Core star differs')
    for patch in f['patches']:
        seam, hidden = set(patch['attachment']), set(patch['new_vertices'])
        require(len(seam) == 3 and len(hidden) == 9 and not seam & hidden,
                'Patch carrier differs')
        require(all(v in whole[u] for u, v in combinations(seam, 2)), 'Seam is not a triangle')
        require(all(whole[v] <= hidden | seam for v in hidden), 'Patch leaks across seam')
        require(set(whole) - hidden - seam, 'No other side of separator')

    states = [dict(enumerate(f['states'][0]))]
    proper(exterior, states[0])
    require([states[0][v] for v in range(12)] == base['colouring'], 'Initial restriction differs')
    history = []
    for index, command in enumerate(f['commands']):
        new, support = switch(exterior, states[-1], command['pair'], command['root'])
        walk = f['chains'][index]
        require(set(walk) == support and walk[0] == command['root'], 'Component walk differs')
        require(all(v in exterior[u] for u, v in zip(walk, walk[1:])), 'Disconnected walk')
        require([new[v] for v in range(n)] == f['states'][index + 1], 'Physical endpoint differs')
        history.append({'pair': command['pair'], 'support_size': len(support)})
        states.append(new)
    final = states[-1] | {n + i: a for i, a in enumerate(f['final_core'])}
    proper(whole, final)
    profile, _ = direct_solver(source, ring, (1, 6))
    scores = [profile(tuple(c[v] for v in range(ring)))[0] for c in states]
    require(scores == [(1, -4), (1, -1), (0, -1)], 'Escape profiles differ')

    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripAnchorPadding.lean'
    text = lean.read_text()
    for name, expected in [('star', f['whole_rows']), ('neighbours', f['neighbours']),
                           ('tour', f['whole_tour']), ('repairChain', f['chains'])]:
        actual = json.loads(definition(text, name).removeprefix('!'))
        require(actual == expected, 'Lean literal differs: ' + name)
    require(all(set(f['whole_rows'][v]) == whole[v] for v in whole), 'Whole row differs')
    require(all(set(f['neighbours'][v]) == exterior[v] for v in exterior), 'Exterior row differs')
    values = definition(text, 'values')
    for i, row in enumerate(f['states']):
        require(f'|{i}=>![' + ','.join('c' + str(a) for a in row) + ']' in values,
                'Lean colouring differs')
    return {
        'classification': 'MINIMUM_DEGREE_FIVE_GUARDED_ANCHOR_TRAP',
        'source': 'D0099', 'source_sha256': f['source_sha256'],
        'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
        'attribution': 'Yuta Inoue D0099 catalogue, MIT; source semantics from Gonthier/Emery.',
        'exterior_vertices': n, 'whole_vertices': len(whole),
        'whole_degree_counts': dict(sorted(Counter(map(len, whole.values())).items())),
        'separating_triangles': [p['attachment'] for p in f['patches']],
        'escape': history, 'scores': scores,
        'evidence': 'Lean proves homomorphism transport of the arbitrary-history obstruction, '
                    'spherical rotation geometry, minimum degree five, exact source stars, '
                    'a separating seam, and physical two-switch reconstruction.',
        'limits': ['Separating triangles remain; easy separator reduction is available.',
                   'No counterexample without short separating cycles is established.',
                   'Only the stated guarded policy is refuted; the example is four-colourable.',
                   'No strict reduction, universal coverage or classical dependency removal is claimed.'],
        'fixture_sha256': sha256(path.read_bytes()).hexdigest(),
        'lean_sha256': sha256(lean.read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
