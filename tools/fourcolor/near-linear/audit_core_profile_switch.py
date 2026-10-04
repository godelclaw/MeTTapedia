#!/usr/bin/env python3
"""Replay the core-list summary counterexample on its actual planar exterior.

The Lean modules independently check the geometry, the physical components,
reconstruction and nonextension. This small program cross-checks the fixture
against the pinned source without enumerating all boundary words.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_cycle_blocks import sphere
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_two_port_core import eliminate


def profile(patch, ring, word):
    return [sum(1 << c for c in set(range(4)) -
                {word[j] for j in patch[v] if j < ring})
            for v in range(ring, len(patch))]


def verify(here):
    path = here / 'core-profile-switch-example.json'
    data = json.loads(path.read_text())
    source = here / (data['source']['configuration'] + '.conf')
    require(sha256(source.read_bytes()).hexdigest() == data['source']['sha256'],
            'Source pin differs')
    ring, patch = graph(source.read_bytes())
    require((ring, len(patch)) == (11, 18), 'Source size differs')
    faces = [tuple(f) for f in data['source_inner_faces']]
    faces += [(a, c, b) for a, b, c in data['exterior_faces']]
    ambient = sphere(faces)
    require(set(ambient) == set(range(18)), 'Ambient carrier differs')
    require(all(patch[v] <= ambient[v] for v in range(18)), 'Source edge lost')
    require(all(patch[v] == ambient[v] for v in range(ring, 18)), 'Core acquired edges')
    exterior = {v: ambient[v] & set(range(ring)) for v in range(ring)}
    profiles, switched, supports = [], [], []
    for i, word in enumerate(data['initial']):
        colouring = dict(enumerate(word))
        proper(exterior, colouring)
        lists = profile(patch, ring, word)
        require(lists == data['expected_profile_masks'], 'Initial profiles differ')
        # Core vertices 12 and 13 are adjacent and both forced to colour zero.
        require(lists[1] == lists[2] == 1 and 13 in patch[12], 'Initial conflict lost')
        require(eliminate(patch, ring, word)[0] is None, 'Initial word extends')
        after, support = switch(exterior, colouring, data['pair'], data['root'])
        actual = [after[v] for v in range(ring)]
        require(actual == data['expected_after'][i], 'Switched word differs')
        require(sorted(support) == data['expected_components'][i], 'Component differs')
        profiles.append(lists)
        switched.append(actual)
        supports.append(sorted(support))
    core, _ = eliminate(patch, ring, switched[0])
    require(core is not None, 'First switched word has no reconstructed witness')
    whole = dict(enumerate(switched[0] + data['first_core_witness']))
    proper(ambient, whole)
    second_lists = profile(patch, ring, switched[1])
    require(second_lists[1] == second_lists[2] == 1, 'Second conflict lost')
    require(eliminate(patch, ring, switched[1])[0] is None, 'Second switched word extends')
    command = data['preparation']
    prepared, support = switch(exterior, dict(enumerate(data['initial'][1])),
                               command['pair'], command['root'])
    require(sorted(support) == command['component'], 'Preparation component differs')
    require(list(prepared.values()) == data['initial'][0], 'Preparation misses the first input')
    final, _ = switch(exterior, prepared, data['pair'], data['root'])
    require(list(final.values()) == switched[0], 'Composed physical history differs')
    return {
        'evidence': 'Independent finite replay; the corresponding statements are Lean checked.',
        'fixture_sha256': sha256(path.read_bytes()).hexdigest(),
        'ambient_vertices': len(ambient), 'ambient_darts': sum(map(len, ambient.values())),
        'exterior_vertices': len(exterior), 'exterior_edges': sum(map(len, exterior.values())) // 2,
        'same_initial_core_lists': profiles[0] == profiles[1],
        'initial_profile_masks': profiles[0], 'components': supports,
        'after': switched, 'after_profiles': [profile(patch, ring, w) for w in switched],
        'first_reconstructed_colouring': list(whole.values()),
        'preparation_component': sorted(support),
        'physical_history_lengths': [1, 2],
        'both_initial_colourings_repaired': True,
        'second_conflict': {'edge': [12, 13], 'forced_colour': 0},
        'scope': 'Failure of a deterministic rooted-switch update from core lists alone. '
                 'No claim about impossibility of richer repair interfaces or compact coverage.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
