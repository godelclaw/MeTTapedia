#!/usr/bin/env python3
"""Replay fixed-pair obstruction and two-switch repair on the flat-triangle sphere.

Lean checks the spherical rotation, degree bounds, exact exterior and source
incidence, arbitrary-length fixed-pair obstruction and physical reconstruction.
Flat charges and all short-cycle exclusions are independent program checks.
"""
import argparse
import ast
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

from audit_closing_triangle_strips import catalogue_inventory, replay_faces, verify as verify_geometry
from audit_boundary_observation import components, proper, switch
from audit_component_detach import chain
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_strip_partial import partial
from probe_flat_pairs import geometry


def verify(here, catalogue):
    fixture_path = here / 'strip-sphere-phase-example.json'
    fixture = json.loads(fixture_path.read_text())
    original_path = here / fixture['source_fixture']
    require(sha256(original_path.read_bytes()).hexdigest() == fixture['source_fixture_sha256'],
            'Changed geometric source')
    original = json.loads(original_path.read_text())
    decoded, family, _, _ = catalogue_inventory(catalogue, original)
    geometric = verify_geometry(here, catalogue, original, decoded, family)
    faces = replay_faces(original)
    _, ambient, nxt, _ = geometry(faces)
    image = original['source_occurrence']['images']
    removed = set(image[11:])
    carrier = sorted(set(ambient) - removed)
    position = {v: i for i, v in enumerate(carrier)}
    exterior = {position[v]: {position[w] for w in ambient[v] if w in position} for v in carrier}
    ports = [position[v] for v in image[:11]]
    values = fixture['colouring']
    require(len(values) == 162 and {v for v, c in enumerate(values) if c is None} == removed,
            'Wrong deleted vertices')
    initial = {position[v]: c for v, c in enumerate(values) if c is not None}
    proper(exterior, initial)
    ring, source = graph((here / 'D0099.conf').read_bytes())
    require(ring == 11, 'Wrong source boundary')
    word = lambda c: [c[v] for v in ports]
    minimum = lambda w: next(k for k in range(4) if any(
        partial(source, ring, w, holes) is not None for holes in combinations(range(8), k)))
    require(minimum(word(initial)) == 2, 'Initial defect differs')
    counts = []
    partitions = []
    for a, b in combinations(range(4), 2):
        blocks = [s for s in components(exterior, initial, (a, b)) if s & set(ports)]
        partitions.append(sorted(sorted(ports.index(v) for v in s if v in ports) for s in blocks))
        for mask in range(1 << len(blocks)):
            c = dict(initial)
            for j, support in enumerate(blocks):
                if mask >> j & 1:
                    for v in support:
                        c[v] ^= a ^ b
            require(all(partial(source, ring, word(c), holes) is None
                        for k in (0, 1) for holes in combinations(range(8), k)),
                    'A fixed-pair phase improves')
        counts.append(1 << len(blocks))
    old = json.loads((here / 'strip-phase-audit.json').read_text())
    require(partitions == [r['boundary_blocks'] for r in old['fixed_pair_phases']],
            'The shared route profile changed')
    states = [initial]
    chains = []
    for command in fixture['commands']:
        c, support = switch(exterior, states[-1], command['pair'], position[command['root']])
        states.append(c)
        chains.append(chain(exterior, support, position[command['root']]))
    require(len(chains) == 2 and [minimum(word(c)) for c in states] == [2, 2, 0],
            'The repair profile differs')
    completed = complete_patch(source, word(states[-1]))
    require(completed is not None, 'No source reconstruction')
    final = {v: states[-1][position[v]] if v in position else completed[image.index(v)]
             for v in ambient}
    proper(ambient, final)
    # Compare every literal used by the Lean consumer with this independent replay.
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripSpherePhase.lean'
    text = lean.read_text()
    def definition(name):
        m = re.search(rf'^def {name}\b(.*?)(?=^(?:def |theorem |instance |private |/--|noncomputable |end ))',
                      text, re.M | re.S)
        require(m is not None, f'Missing Lean definition {name}')
        return re.sub(r'\s+', '', m[1])
    def literal(name):
        return ast.literal_eval(definition(name).split(':=', 1)[1].replace('!', ''))
    rows = []
    for v in range(162):
        row = [min(ambient[v])]
        while nxt[v, row[-1]] != row[0]:
            row.append(nxt[v, row[-1]])
        rows.append(row)
    for name, expected in [('star', rows), ('includeExterior', carrier), ('image', image),
                           ('ports', ports), ('neighbors', [sorted(exterior[v]) for v in range(154)]),
                           ('repairChain', chains)]:
        require(literal(name) == expected, f'Lean {name} differs')
    colour_row = lambda xs: '![' + ','.join('c' + str(c) for c in xs) + ']'
    for i, c in enumerate(states):
        require(f'|{i}=>' + colour_row(c[v] for v in range(154)) in definition('values'),
                'Lean state differs')
    require(definition('finalValues').split(':=', 1)[1] == colour_row(final[v] for v in range(162)),
            'Lean final colouring differs')
    return {
        'classification': 'SPHERICAL_SHARED_PHASE_OBSTRUCTION_AND_TWO_SWITCH_REPAIR',
        'fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(),
        'geometric_source_sha256': fixture['source_fixture_sha256'],
        'source_sha256': sha256((here / 'D0099.conf').read_bytes()).hexdigest(),
        'catalogue_revision': original['catalogue']['revision'],
        'attribution': 'Yuta Inoue catalogue, MIT; Gonthier/Emery semantics and cubic Euler theorem.',
        'ambient_vertices': 162, 'exterior_vertices': 154,
        'degree_range': [min(map(len, ambient.values())), max(map(len, ambient.values()))],
        'geometric_replay': geometric,
        'same_initial_boundary_partitions_as_smaller_example': True,
        'fixed_pair_boundary_endpoints': counts,
        'minimum_holes': [minimum(word(c)) for c in states],
        'physical_component_sizes': [len(set(c)) for c in chains],
        'commands': fixture['commands'],
        'whole_colouring_reconstructed': True,
        'formal_scope': 'Planar triangular ambient rotation, degree bounds, complete source stars, exact induced exterior, arbitrary-length fixed-pair obstruction, physical mixed-pair reconstruction.',
        'program_only_geometry': 'Three flat degree-seven centres and absence of obstructing cycles of length three through five; no whole flat ball is claimed.',
        'limits': ['No general obstruction to mixed-pair repair.', 'One supplied occurrence, no geometric supply or catalogue reduction.', 'This is a colourable test map satisfying the checked local hypotheses, not a minimal counterexample to Four Colour.'],
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalogue', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent, args.catalogue)
    payload = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
