#!/usr/bin/env python3
"""Check which boundary separation makes a prepared pivot useful.

Lean proves the exact source extension law and consumes a physical repair.
This program independently checks complementary boundary partitions, one
positive and one negative pivot, and a bounded supply census. It does not
certify a universal planar supply theorem.
"""
import argparse
from collections import deque
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_cascading_detach import phase_words
from audit_clique_fill import make_profile, source_faces
from audit_component_detach import PAIRS, data
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_odd_mesh import refine, cycle_census
from audit_two_port_core import eliminate
from probe_flat_pairs import geometry

PARTITIONS = ((0,0,0), (0,0,1), (0,1,0), (0,1,1), (0,1,2))
RUNS = ((2,), (5,), (7,8,9,10))
COMPLEMENT = ((0,1), (3,4), (6,))


def blocks(runs, labels):
    return [set().union(*(set(runs[i]) for i in range(3) if labels[i] == lab))
            for lab in sorted(set(labels))]


def crosses(left, right):
    return any((a in left and b in right and c in left and d in right) or
               (a in right and b in left and c in right and d in left)
               for a,b,c,d in combinations(range(11), 4))


def partition(adj, col, ports, pair):
    return sorted(sorted(i for i,v in enumerate(ports) if v in s)
                  for s in components(adj, col, pair) if s.intersection(ports))


def path(adj, col, pair, start, end):
    routes, todo = {start: [start]}, deque([start])
    while todo:
        x = todo.popleft()
        for y in sorted(adj[x]):
            if col[y] in pair and y not in routes:
                routes[y] = routes[x] + [y]
                todo.append(y)
    return routes.get(end)


def census(adj, ports, initial, profile):
    proper(adj, initial)
    protected = set(ports)
    threshold = profile([initial[v] for v in ports])
    preparations = [(None, None, initial)]
    for pair in PAIRS:
        for support in components(adj, initial, pair):
            if not protected & support:
                preparations.append((pair, min(support), switch(adj, initial, pair, min(support))[0]))
    result = []
    for pair, root, prepared in preparations:
        for v in sorted(set(adj) - protected):
            used = {prepared[u] for u in adj[v]}
            for dest in sorted(set(range(4)) - used - {prepared[v]}):
                target, actual = switch(adj, prepared, (prepared[v], dest), v)
                require(actual == {v}, 'The pivot is not a singleton component')
                proper(adj, target)
                good = phase_words(adj, target, ports, profile, threshold)
                merges = []
                for other in sorted(set(range(4)) - {prepared[v], dest}):
                    old = [s & protected for s in components(adj, prepared, (dest, other))]
                    new = next(s for s in components(adj, target, (dest, other)) if v in s)
                    hits = [sorted(ports.index(x) for x in s) for s in old if s & new]
                    if len(hits) > 1:
                        merges.append({'pair': [dest, other], 'old_boundary_blocks': hits})
                result.append({'preparation': None if pair is None else [list(pair), root],
                               'pivot': v, 'degree': len(adj[v]), 'old_colour': prepared[v],
                               'new_colour': dest, 'boundary_merges': merges,
                               'extending_phase_outcomes': sum(g['extends'] for g in good)})
    return {'preparations_including_identity': len(preparations), 'pivots': len(result),
            'pivots_allowing_extension': sum(r['extending_phase_outcomes'] > 0 for r in result),
            'pivots_merging_boundary_blocks': sum(bool(r['boundary_merges']) for r in result),
            'merging_pivots_without_extending_phase': sum(bool(r['boundary_merges']) and
                not r['extending_phase_outcomes'] for r in result)}, result


def verify(here):
    f, ambient, adj, ports, initial, profile, *_ = data(here)
    ring, patch = graph((here / f['configuration']).read_bytes())
    word = [initial[v] for v in ports]
    require(word == [1,3,2,3,1,0,3,0,2,0,2], 'Different boundary class')
    choices = []
    for a,b,c in product((False,True), repeat=3):
        bits = (a,b,c)
        changed = [2-col if col in (0,2) and bits[0 if j == 2 else 1 if j == 5 else 2]
                   else col for j,col in enumerate(word)]
        witness, _ = eliminate(patch, ring, changed)
        require((witness is not None) == (a == b and b != c), 'Core law differs')
        if witness is not None:
            predicted = [1, 0 if b else 2, 1, 3, 0 if c else 2, 3, 2 if c else 0]
            require([witness[v] for v in range(11,18)] == predicted, 'Symbolic witness differs')
        choices.append({'choices': bits, 'extends': witness is not None})
    compatible = []
    for left,right in product(PARTITIONS, repeat=2):
        ls, rs = blocks(RUNS, left), blocks(COMPLEMENT, right)
        if any(crosses(s,t) for s in ls for t in rs):
            continue
        extends = left[2] != left[0] and left[2] != left[1]
        crosscut = right[0] == right[2]
        require(not crosscut or extends, 'Complementary crosscut did not separate the target run')
        compatible.append({'zero_two': left, 'one_three': right,
                           'crosscut_1_to_6': crosscut, 'phase_extends': extends})
    require(len(compatible) == 12, 'Boundary partition census changed')
    prepared, _ = switch(adj, initial, (1,2), 133)
    target, singleton = switch(adj, prepared, (0,1), 43)
    require(singleton == {43}, 'Positive pivot changed')
    route = path(adj, target, (1,3), ports[1], ports[6])
    require(route is not None and 43 in route, 'Missing complementary route through the pivot')
    require(path(adj, prepared, (1,3), ports[1], ports[6]) is None, 'Crosscut already existed')
    require(all(target[v] in (1,3) for v in route) and
            all(v in adj[u] for u,v in zip(route,route[1:])), 'Invalid complementary route')
    final, _ = switch(adj, target, (0,2), 7)
    witness, _ = eliminate(patch, ring, [final[v] for v in ports])
    require(witness is not None, 'Physical repair failed')
    proper(ambient, final | {f['images'][v]: col for v,col in witness.items()})
    rows, retained = census(adj, ports, initial, profile)
    require(rows['pivots'] == 3 and rows['pivots_allowing_extension'] == 1, 'Retained census changed')
    bad = next(r for r in retained if r['pivot'] == 87)
    require(bad['boundary_merges'] and bad['extending_phase_outcomes'] == 0, 'Negative control failed')
    # Each further sample retains an exact source and oriented sphere. No
    # universal supply claim follows from success on these four samples.
    mesh_fixture = json.loads((here / 'odd-mesh-example.json').read_text())
    require(sha256((here / mesh_fixture['source_fixture']).read_bytes()).hexdigest() ==
            mesh_fixture['source_fixture_sha256'], 'Mesh source pin changed')
    source = json.loads((here / mesh_fixture['source_fixture']).read_text())
    for pin in source['sources']:
        require(sha256((here / pin['file']).read_bytes()).hexdigest() == pin['sha256'],
                'Configuration source pin changed')
    mesh = []
    for base in source['cases']:
        raw = (here / base['configuration']).read_bytes()
        n, p = graph(raw)
        inside = set(range(n, len(p)))
        for width in (5,7):
            faces, col, *_ = refine(base['outer_faces'], dict(enumerate(base['boundary'])), len(p), width)
            sphere = source_faces(raw) + faces
            _, whole, _, _ = geometry(sphere)
            geom = cycle_census(sphere)
            require(geom['minimum_degree'] >= 5 and geom['obstructing_cycles'] == 0,
                    'A mesh sample has an excluded short separator')
            exterior = {v: ns-inside for v,ns in whole.items() if v not in inside}
            summary, _ = census(exterior, list(range(n)), col, make_profile(p,n))
            mesh.append({'configuration': base['configuration'], 'width': width,
                         'exterior_vertices': len(exterior), **summary})
    root = here.parents[2]
    return {'evidence': 'The core law and selected physical source consumer are Lean checked. '
            'Crosscut interpretation, bounded supply census and negative pivot are program evidence.',
        'source_sha256': sha256((here / f['configuration']).read_bytes()).hexdigest(),
        'base_fixture_sha256': sha256((here / 'component-detach-example.json').read_bytes()).hexdigest(),
        'lean_sha256': sha256((root / 'lean/fourcolor-classical/MettapediaFourColor/ThreeBlockCore.lean').read_bytes()).hexdigest(),
        'core_choices': choices, 'compatible_noncrossing_partitions': compatible,
        'positive_crosscut': {'boundary_ports': [1,6], 'pair': [1,3], 'route': route,
            'after_pivot_partition': partition(adj,target,ports,(0,2))},
        'retained_census': rows, 'retained_pivots': retained, 'mesh_census': mesh,
        'scope': 'A merge of arbitrary boundary blocks does not guarantee extension after one following '
            'fixed-pair phase. The negative census covers all phase boundary outcomes, not arbitrary mixed '
            'histories. The useful 1/3 crosscut gives a sufficient abstract noncrossing condition; '
            'its general planar bridge and geometric supply are not yet Lean proved. '
            'No coverage entry or existing complete-proof dependency is removed.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
