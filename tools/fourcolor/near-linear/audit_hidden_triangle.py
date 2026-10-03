#!/usr/bin/env python3
"""Verify two hidden-triangle fibre obstructions without exploring histories.

The complete-sphere witness has ambient degrees five through seven. Proper
endpoints agree outside a facial triangle. A graph homomorphism from the
kernel-certified frozen observer proves that their physical classes differ.
"""
import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_chain_boundary import subdivide
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_frozen_observer import OBSERVER_EDGES, OBSERVER_INITIAL
from audit_independent_repair import availability, complete_patch, verify_case as verify_repair
from probe_flat_pairs import geometry, initial_faces


def verify(here):
    path = here / 'hidden-triangle-example.json'
    fixture = json.loads(path.read_text())
    source = here / fixture['source']
    require(sha256(source.read_bytes()).hexdigest() == fixture['source_sha256'], 'Source pin differs')
    sources = json.loads(source.read_text())['cases']
    require(len(fixture['cases']) == 2, 'Expected an exterior and a complete-sphere witness')
    records = []
    checked = set()
    for witness in fixture['cases']:
        case = sources[witness['source_case']]
        if witness['source_case'] not in checked:
            verify_repair(here, case)
            checked.add(witness['source_case'])
        spherical = json.loads((here / case['source_fixture']).read_text())
        original = json.loads((here / spherical['source_fixture']).read_text())
        faces = subdivide(initial_faces())
        for a, b, c, d in original['edge_flip_history'][:spherical['edge_flip_prefix']]:
            darts, _, _, _ = geometry(faces)
            i, ac = darts[a, b]
            j, ad = darts[b, a]
            require((ac, ad) == (c, d), 'Source flip differs')
            faces[i], faces[j] = (c, d, b), (d, c, a)
        _, ambient, _, _ = geometry(faces)
        occurrence = spherical['source_occurrence']
        ring, patch = graph((here / occurrence['configuration']).read_bytes())
        ports = occurrence['images'][:ring]
        removed = set(occurrence['images'][ring:])
        exterior = {v: ns - removed for v, ns in ambient.items() if v not in removed}
        current = {v: c for v, c in enumerate(case['colouring']) if c is not None}
        require(witness['stage'] in ['initial_exterior', 'final_sphere'], 'Unknown stage')
        adj = exterior
        if witness['stage'] == 'final_sphere':
            independent = set(case['hidden'])
            near = {v: ns - independent for v, ns in exterior.items() if v not in independent}
            for command in case['commands']:
                a, b = command['pair']
                small = {v: current[v] for v in near}
                chosen = set()
                for root in command['roots']:
                    _, support = switch(near, small, command['pair'], root)
                    require(not chosen & support, 'Component chosen twice')
                    chosen |= support
                target = {v: (b if c == a else a) if v in chosen else c for v, c in small.items()}
                allowed = availability(exterior, independent, target)
                require(all(allowed.values()), 'Source repair does not extend')
                for v, colours in allowed.items():
                    target[v] = current[v] if current[v] in colours else min(colours)
                proper(exterior, target)
                current = target
            completion = complete_patch(patch, [current[v] for v in ports])
            require(completion is not None, 'Original patch did not reconstruct')
            current.update((occurrence['images'][i], completion[i]) for i in range(ring, len(completion)))
            adj = ambient
        proper(adj, current)
        hidden = witness['hidden']
        require(len(hidden) == len(set(hidden)) == 3 and set(hidden) <= exterior.keys(),
                'Hidden triangle must have three actual exterior vertices')
        require(not set(hidden) & set(ports), 'A patch port was hidden')
        require(frozenset(hidden) in {frozenset(face) for face in faces}, 'Hidden triangle is not facial')
        require(len(witness['target_hidden']) == 3, 'Missing hidden target colours')
        target = dict(current)
        target.update(zip(hidden, witness['target_hidden']))
        proper(adj, target)
        boundary = set(adj) - set(hidden)
        require(all(current[v] == target[v] for v in boundary), 'Retained word differs')
        images, palette = witness['observer_images'], witness['palette']
        require(len(images) == 9 and set(images) <= adj.keys(), 'Invalid observer carrier')
        require(sorted(palette) == list(range(4)), 'Invalid palette permutation')
        require(set(images[:3]) == set(hidden), 'Wrong observed core')
        require(set(images[3:]) <= boundary, 'An observer boundary vertex was hidden')
        require(all(images[v] in adj[images[u]] for u, v in OBSERVER_EDGES),
                'Observer is not a graph homomorphism')
        require([current[v] for v in images] == [palette[c] for c in OBSERVER_INITIAL],
                'Initial observation is not the frozen pattern')
        require(target[images[2]] != palette[1], 'Observed core did not change')
        allowed = [set(range(4)) - {current[y] for y in adj[x] & boundary} for x in hidden]
        # Only proper assignments to three fixed vertices are counted here;
        # the obstruction to histories is supplied by the observer theorem.
        assignments = [list(cs) for cs in product(*map(sorted, allowed))
                       if all(cs[i] != cs[j] for i in range(3) for j in range(i)
                              if hidden[j] in adj[hidden[i]])]
        require(len(assignments) == 2, 'Expected the explicit two-state fibre')
        require([current[v] for v in hidden] in assignments and witness['target_hidden'] in assignments,
                'Endpoints do not exhaust the fibre')
        records.append({'stage': witness['stage'], 'configuration': occurrence['configuration'],
                        'vertices': len(adj), 'degree_range': [min(map(len, adj.values())), max(map(len, adj.values()))],
                        'hidden_triangle': hidden, 'hidden_degrees': [len(adj[v]) for v in hidden],
                        'facial_triangle': True, 'retained_vertices': len(boundary),
                        'same_retained_colouring': True, 'proper_endpoints': True,
                        'allowed_hidden_colours': [sorted(s) for s in allowed],
                        'all_hidden_assignments': assignments,
                        'observer_images': images, 'observer_distinct_vertices': len(set(images)),
                        'observer_degrees': [len(adj[v]) for v in images],
                        'protected_frozen_observer_verified': True,
                        'distinct_physical_classes_by_observer': True,
                        'concrete_instance_kernel_certified': False})
    return {'evidence': 'Exact program verification of the premises of a kernel-proved frozen-fibre theorem.',
            'cases': records,
            'kernel_theorems': ['Mettapedia.GraphTheory.FourColor.FrozenFibreObserver.not_fibres',
                               'Mettapedia.GraphTheory.FourColor.FrozenFibreObserver.not_fibration'],
            'scope': 'Refutes exact history lifting between arbitrary specified extensions after forgetting '
                     'the hidden physical class. Does not refute existence of a successful colouring, '
                     'class-aware interfaces, a larger moving context or a different decomposition. '
                     'Minimal-counterexample hypotheses and geometric coverage are not asserted.',
            'fixture_sha256': sha256(path.read_bytes()).hexdigest(),
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
            'credited_compression': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
