#!/usr/bin/env python3
"""Replay failure of a deterministic update of current boundary partitions.

The spherical examples retain the full punctured exterior, including vertices
far from the ports. Geometry is independently checked by the existing fixture
audit. A separate four-cycle theorem in Lean proves the general obstruction;
the spherical applications here are exact program evidence.
"""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from audit_chain_boundary import subdivide
from audit_diamond_sources import require, read_rows
from audit_flat_seven_return import verify as verify_sphere
from probe_flat_pairs import geometry, initial_faces


def components(adj, colouring, pair):
    unseen = {v for v in adj if colouring[v] in pair}
    result = []
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        support, todo = {root}, [root]
        while todo:
            v = todo.pop()
            new = adj[v] & unseen
            unseen -= new
            support |= new
            todo.extend(new)
        result.append(support)
    return result


def observe(adj, colouring, ports):
    word = tuple(colouring[v] for v in ports)
    partitions = []
    for pair in combinations(range(4), 2):
        blocks = [tuple(i for i, v in enumerate(ports) if v in support)
                  for support in components(adj, colouring, pair)]
        partitions.append(tuple(sorted(block for block in blocks if block)))
    return word, tuple(partitions)


def switch(adj, colouring, pair, root):
    require(len(pair) == 2 and pair[0] != pair[1] and
            all(c in range(4) for c in pair), 'Invalid colour pair')
    require(root in adj and colouring[root] in pair, 'Inactive root')
    support = next(s for s in components(adj, colouring, pair) if root in s)
    a, b = pair
    result = {v: (b if c == a else a) if v in support else c
              for v, c in colouring.items()}
    proper(adj, result)
    return result, support


def proper(adj, colouring):
    require(set(colouring) == set(adj), 'Missing exterior vertex')
    require(all(c in range(4) for c in colouring.values()), 'Invalid colour')
    require(all(colouring[v] != colouring[w] for v in adj for w in adj[v]),
            'Improper exterior colouring')


def verify_case(here, case):
    path = here / case['source_fixture']
    require(sha256(path.read_bytes()).hexdigest() == case['source_fixture_sha256'],
            'Sphere fixture pin changed')
    base_result = verify_sphere(here, path.name)
    fixture = json.loads(path.read_text())
    original = json.loads((here / fixture['source_fixture']).read_text())
    faces = subdivide(initial_faces())
    for a, b, c, d in original['edge_flip_history'][:fixture['edge_flip_prefix']]:
        darts, _, _, _ = geometry(faces)
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d), 'Incorrect flip geometry')
        faces[i], faces[j] = (c, d, b), (d, c, a)
    _, ambient, _, _ = geometry(faces)
    occurrence = fixture['source_occurrence']
    _, ring = read_rows((here / occurrence['configuration']).read_text())[0]
    ports = occurrence['images'][:ring]
    removed = set(occurrence['images'][ring:])
    adj = {v: ws - removed for v, ws in ambient.items() if v not in removed}
    require(len(case['colouring']) == len(ambient), 'Wrong ambient carrier')
    require({v for v, c in enumerate(case['colouring']) if c is None} == removed,
            'Deleted vertices differ from the actual core')
    left = {v: c for v, c in enumerate(case['colouring']) if c is not None}
    proper(adj, left)
    right, hidden = switch(adj, left, case['hidden_pair'], case['hidden_root'])
    require(not hidden & set(ports), 'Preparatory switch touches a port')
    before = observe(adj, left, ports)
    require(before == observe(adj, right, ports), 'Initial summaries differ')
    require(0 <= case['action_port'] < len(ports), 'Invalid action port')
    root = ports[case['action_port']]
    after_left, support_left = switch(adj, left, case['action_pair'], root)
    after_right, support_right = switch(adj, right, case['action_pair'], root)
    first, second = observe(adj, after_left, ports), observe(adj, after_right, ports)
    require(first[0] == second[0], 'Boundary colours changed differently')
    require(first[1] != second[1], 'No future partition difference')
    differences = [{'pair': list(pair), 'left': a, 'right': b}
                   for pair, a, b in zip(combinations(range(4), 2), first[1], second[1])
                   if a != b]
    second_action = None
    for pair in combinations(range(4), 2):
        for i, root in enumerate(ports):
            if after_left[root] not in pair:
                continue
            end_left, _ = switch(adj, after_left, pair, root)
            end_right, _ = switch(adj, after_right, pair, root)
            word_left = [end_left[v] for v in ports]
            word_right = [end_right[v] for v in ports]
            if word_left != word_right:
                second_action = {'pair': list(pair), 'port': i,
                                 'left_word': word_left, 'right_word': word_right}
                break
        if second_action:
            break
    require(second_action is not None, 'No second command exposes the lost distinction')
    return {
        'source_fixture': path.name,
        'configuration': occurrence['configuration'],
        'ambient_vertices': len(ambient), 'exterior_vertices': len(adj), 'ports': ring,
        'ambient_degree_range': [min(map(len, ambient.values())), max(map(len, ambient.values()))],
        'flat_centres': base_result['centres'],
        'obstructing_short_cycles': base_result['obstructing_short_cycles'],
        'first_stage_colourings_checked': 4,
        'hidden_component_size': len(hidden),
        'action_pair': case['action_pair'], 'action_port': case['action_port'],
        'action_component_sizes': [len(support_left), len(support_right)],
        'initial_boundary_and_all_six_partitions_equal': True,
        'final_boundary_equal': True, 'final_partition_differences': differences,
        'second_command_distinguishes_boundary_words': second_action,
        'geometry_kernel_certified': False,
    }


def verify(here):
    path = here / 'flat-seven-observation-example.json'
    fixture = json.loads(path.read_text())
    require(len(fixture['cases']) == 2, 'Expected both actual source fixtures')
    results = [verify_case(here, case) for case in fixture['cases']]
    return {
        'evidence': 'Exact independent program checks on complete punctured exteriors.',
        'cases': results,
        'claim_refuted': 'The current boundary word and all six current pair partitions '
                         'determine their successor under a boundary-rooted component switch.',
        'not_refuted': [
            'Witness-preserving relational transport with silent preparation',
            'A richer compositional interface',
            'Repair using several colour pairs',
            'Coverage under stronger whole-neighbourhood flatness or minimality hypotheses',
            'Compact compositional Four Colour proofs in general',
        ],
        'fixture_sha256': sha256(path.read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'credited_compression': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
