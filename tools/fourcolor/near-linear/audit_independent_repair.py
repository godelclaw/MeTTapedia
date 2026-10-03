#!/usr/bin/env python3
"""Replay exact independent elimination and repair on two spherical exteriors.

Each joint retained switch satisfies all hidden colour-availability clauses.
The lift uses silent preparation, actual full-graph component switches and
silent finishing. The final exterior reconstructs the seven-vertex patch.
The generic lifting law is proved separately in Lean; these consumers and
sphere geometry are independent program checks.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_chain_boundary import subdivide
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_flat_seven_return import verify as verify_sphere
from probe_flat_pairs import geometry, initial_faces


def availability(adj, hidden, colouring):
    return {v: set(range(4)) - {colouring[w] for w in adj[v]} for v in hidden}


def complete_patch(adj, word):
    colours = list(word) + [-1] * (len(adj) - len(word))
    def visit(v):
        if v == len(adj):
            return list(colours)
        for c in range(4):
            if all(colours[w] != c for w in adj[v]):
                colours[v] = c
                answer = visit(v + 1)
                if answer is not None:
                    return answer
                colours[v] = -1
        return None
    return visit(len(word))


def lifted_step(adj, hidden, before, after, pair):
    """Construct the three phases of IndependentLift.partial_swap_avoiding."""
    a, b = pair
    prepared, middle = dict(before), dict(after)
    for v in hidden:
        c, d = before[v], after[v]
        if c not in pair:
            prepared[v] = middle[v] = c
        elif d not in pair:
            prepared[v] = middle[v] = d
    proper(adj, prepared)
    proper(adj, middle)
    fixed = {v for v in adj if v not in hidden and before[v] == after[v]}
    current, phases = dict(before), []
    for name, target in [('prepare', prepared), ('joint', middle), ('finish', after)]:
        moves = []
        while current != target:
            root = min(v for v in current if current[v] != target[v])
            selected = pair if name == 'joint' else [current[root], target[root]]
            next_colouring, support = switch(adj, current, selected, root)
            require(not support & fixed, 'Lift touches a protected retained vertex')
            if name != 'joint':
                require(support == {root} and root in hidden, 'Preparation is not silent')
            require(all(current[v] != target[v] and next_colouring[v] == target[v]
                        for v in support), 'Component does not advance to the target')
            moves.append({'pair': list(selected), 'root': root, 'size': len(support)})
            current = next_colouring
        phases.append({'phase': name, 'switches': moves})
    return phases


def verify_case(here, case):
    source = here / case['source_fixture']
    require(sha256(source.read_bytes()).hexdigest() == case['source_fixture_sha256'],
            'Source pin differs')
    geometry_audit = verify_sphere(here, source.name)
    fixture = json.loads(source.read_text())
    origin = json.loads((here / fixture['source_fixture']).read_text())
    faces = subdivide(initial_faces())
    for a, b, c, d in origin['edge_flip_history'][:fixture['edge_flip_prefix']]:
        darts, _, _, _ = geometry(faces)
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d), 'Incorrect flip')
        faces[i], faces[j] = (c, d, b), (d, c, a)
    _, ambient, _, _ = geometry(faces)
    occurrence = fixture['source_occurrence']
    ring, core = graph((here / occurrence['configuration']).read_bytes())
    images = occurrence['images']
    ports, removed = images[:ring], set(images[ring:])
    exterior = {v: ws - removed for v, ws in ambient.items() if v not in removed}
    require(len(case['colouring']) == len(ambient), 'Wrong colouring carrier')
    require({v for v, c in enumerate(case['colouring']) if c is None} == removed,
            'Deleted core differs')
    hidden = set(case['hidden'])
    require(len(hidden) == len(case['hidden']) and hidden <= exterior.keys(), 'Invalid hidden set')
    require(not hidden & set(ports), 'A reconstruction port was removed')
    require(all(not exterior[v] & hidden for v in hidden), 'Hidden set is not independent')
    retained = {v: ws - hidden for v, ws in exterior.items() if v not in hidden}
    current = {v: c for v, c in enumerate(case['colouring']) if c is not None}
    proper(exterior, current)
    require(complete_patch(core, [current[v] for v in ports]) is None,
            'Initial colouring already reconstructs')
    records = []
    for command in case['commands']:
        pair = command['pair']
        require(len(pair) == 2 and pair[0] != pair[1] and all(c in range(4) for c in pair),
                'Invalid pair')
        small = {v: current[v] for v in retained}
        all_components = components(retained, small, pair)
        chosen, supports = set(), []
        for root in command['roots']:
            require(root in retained and small[root] in pair, 'Inactive retained root')
            support = next(s for s in all_components if root in s)
            require(not support & chosen, 'Component chosen twice')
            chosen |= support
            supports.append(support)
        a, b = pair
        def apply(support):
            return {v: (b if c == a else a) if v in support else c for v, c in small.items()}
        target = apply(chosen)
        proper(retained, target)
        choices = availability(exterior, hidden, target)
        require(all(choices.values()), 'Joint operation violates a hidden constraint')
        individual_failures = sum(not all(availability(exterior, hidden, apply(s)).values())
                                  for s in supports)
        next_colouring = dict(target)
        for v, allowed in choices.items():
            next_colouring[v] = current[v] if current[v] in allowed else min(allowed)
        proper(exterior, next_colouring)
        phases = lifted_step(exterior, hidden, current, next_colouring, pair)
        records.append({'pair': pair, 'retained_components': len(supports),
                        'individual_components_with_invalid_targets': individual_failures,
                        'phases': phases})
        current = next_colouring
    patch = complete_patch(core, [current[v] for v in ports])
    require(patch is not None, 'Final word does not reconstruct')
    require(all(patch[u] != patch[v] for u, ns in enumerate(core) for v in ns),
            'Improper patch witness')
    reconstructed = dict(current)
    reconstructed.update({images[i]: patch[i] for i in range(ring, len(images))})
    proper(ambient, reconstructed)
    return {'source_fixture': source.name, 'configuration': occurrence['configuration'],
            'ambient_vertices': len(ambient), 'exterior_vertices': len(exterior),
            'hidden_vertices': len(hidden), 'retained_vertices': len(retained),
            'availability_clauses': len(hidden), 'clause_widths': sorted({len(exterior[v]) for v in hidden}),
            'flat_centres': geometry_audit['centres'],
            'obstructing_short_cycles': geometry_audit['obstructing_short_cycles'],
            'initial_word_does_not_extend': True, 'joint_operations': records,
            'full_ambient_reconstruction': True, 'patch_witness': patch,
            'geometry_and_consumer_kernel_certified': False}


def verify(here):
    path = here / 'independent-repair-example.json'
    data = json.loads(path.read_text())
    require(len(data['cases']) == 2, 'Expected both spherical consumers')
    return {'evidence': 'Exact program replay of joint operations, physical lifts and actual reconstruction.',
            'cases': [verify_case(here, case) for case in data['cases']],
            'generic_lean_theorem': 'SimpleGraph.KempeIndependentLift.projected_history_iff',
            'scope': 'Two initial exterior colourings. No repair of every exterior colouring, geometric coverage, '
                     'catalogue compression or standalone Four Colour reduction is claimed.',
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
