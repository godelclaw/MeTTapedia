#!/usr/bin/env python3
"""Independently replay a spherical joint-anchor trap and its two-switch escape.

Direct partial-colouring search checks the anchor profile independently of
Lean's triangle elimination. The facial-shore census checks all simple cycles
of lengths three through five, including chorded cycles. That census remains
program evidence; the universal-history obstruction is a separate Lean proof.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_odd_mesh import cycle_census
from audit_strip_anchor_trap import batches, definition, direct_solver, normalize
from audit_strip_phase import geometry


def verify(here):
    path = here / 'strip-strong-anchor-trap-example.json'
    f = json.loads(path.read_text())
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() == f['source_sha256'], 'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19 and f['anchors'] == [1, 6], 'Source carriers')
    adj = geometry(f['faces'], list(range(ring)))
    n = len(adj)
    require(n == 16, 'Exterior carrier')
    source_vertex = lambda v: v if v < ring else n + v - ring
    triangles = [list(t) for t in combinations(range(19), 3)
                 if all(v in source[u] for u, v in combinations(t, 2))]
    glued = f['faces'] + [[source_vertex(v) for v in t] for t in triangles]
    require(sorted(map(sorted, glued)) == sorted(map(sorted, f['whole_faces'])),
            'Glued faces differ')
    whole = geometry(f['whole_faces'], [])
    require(len(whole) == 24 and min(map(len, whole.values())) == 5, 'Sphere degree or size')
    for v in range(n):
        require(whole[v] & set(range(n)) == adj[v], 'Exterior not induced')
    for v in range(ring, len(source)):
        require(whole[source_vertex(v)] == {source_vertex(w) for w in source[v]},
                'Core star differs')
    census = cycle_census(f['whole_faces'])
    require(json.loads(json.dumps(census)) == f['geometry'], 'Cycle census differs')
    require(census['obstructing_cycles'] == 0, 'Short separating cycle found')

    initial = tuple(f['colouring'])
    proper(adj, dict(enumerate(initial)))
    profile, _ = direct_solver(source, ring, (1, 6))
    score, costs = profile(initial[:ring])
    require(score == (1, -4) and costs == f['initial_costs'], 'Initial profile')
    scores = Counter()
    palette = 0
    for out, _, _, _ in batches(adj, initial):
        sc, cs = profile(out[:ring])
        same = normalize(out) == normalize(initial)
        require(same or (sc[0] > 0 and cs.count(1) < 4), 'Guarded escape found')
        scores[sc] += 1
        palette += same
    require(sum(scores.values()) == 40 and palette == 12, 'Batch counts')
    require([{'score': list(s), 'count': c} for s, c in sorted(scores.items())]
            == f['phase_counts'], 'Batch profiles differ')
    for perm in permutations(range(4)):
        renamed = tuple(perm[a] for a in initial)
        require(profile(renamed[:ring])[0] == score, 'Palette covariance')
        for out, _, _, _ in batches(adj, renamed):
            sc, cs = profile(out[:ring])
            require(normalize(out) == normalize(initial) or (sc[0] > 0 and cs.count(1) < 4),
                    'Renamed guarded escape found')

    states = [dict(enumerate(initial))]
    history = []
    for i, cmd in enumerate(f['commands']):
        new, support = switch(adj, states[-1], cmd['pair'], cmd['root'])
        walk = f['chains'][i]
        require(set(walk) == support and walk[0] == cmd['root'], 'Component walk differs')
        require(all(v in adj[u] for u, v in zip(walk, walk[1:])), 'Disconnected walk')
        require([new[v] for v in range(n)] == f['states'][i+1], 'Physical endpoint differs')
        history.append({'pair': cmd['pair'], 'support': sorted(support)})
        states.append(new)
    scores = [profile(tuple(c[v] for v in range(ring)))[0] for c in states]
    require(scores == [(1, -4), (1, -3), (0, -1)], 'Escape profiles differ')
    proper(whole, states[-1] | {n+i: a for i, a in enumerate(f['final_core'])})

    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripStrongAnchorTrap.lean'
    text = lean.read_text()
    for name, expected in [('star', f['whole_rows']), ('neighbours', f['neighbours']),
                           ('tour', f['whole_tour']), ('repairChain', f['chains'])]:
        require(json.loads(definition(text, name).removeprefix('!')) == expected,
                'Lean literal differs: ' + name)
    for v in whole:
        require(set(f['whole_rows'][v]) == whole[v], 'Whole adjacency row differs')
    for v in adj:
        require(set(f['neighbours'][v]) == adj[v], 'Exterior row differs')
    for face in f['whole_faces']:
        for u, v, w in zip(face, face[1:] + face[:1], face[2:] + face[:2]):
            row = f['whole_rows'][v]
            require(row[(row.index(u)+1) % len(row)] == w, 'Lean cyclic order differs')
    values = definition(text, 'values')
    for i, row in enumerate(f['states']):
        require(f'|{i}=>![' + ','.join('c'+str(a) for a in row) + ']' in values,
                'Lean colouring differs')
    require(definition(text, 'finalCore') == '![' +
            ','.join('c'+str(a) for a in f['final_core']) + ']', 'Lean final core differs')
    return {
        'classification': 'SPHERICAL_GUARDED_ANCHOR_TRAP_WITH_STRONG_CYCLE_CENSUS',
        'source': 'D0099', 'source_sha256': f['source_sha256'],
        'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
        'attribution': 'Yuta Inoue D0099 catalogue, MIT; source semantics from Gonthier/Emery.',
        'whole_vertices': len(whole), 'exterior_vertices': n,
        'whole_degree_counts': dict(sorted(Counter(map(len, whole.values())).items())),
        'component_batches': 40, 'palette_only_batches': palette,
        'palette_permutations_checked': 24, 'cycle_census': census,
        'escape': history, 'scores': scores,
        'evidence': {
            'lean': 'Sphere rotation, minimum degree five, exact source stars, shared '
                    'arbitrary-history obstruction and physical two-switch reconstruction.',
            'program': 'Exact omission costs; complete facial-shore census of all 257 '
                       'simple cycles of length three through five.'},
        'limits': ['The short-cycle census has no Lean semantic bridge yet.',
                   'No zero-charge flatness premise is established.',
                   'Only the stated guarded policy is refuted; two unrestricted switches succeed.',
                   'No strict reduction, universal coverage or catalogue deletion is established.'],
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
