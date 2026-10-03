#!/usr/bin/env python3
"""Check frozen observers in the complete punctured spherical exteriors.

The generic history obstruction is proved in FrozenBoundaryObserver.lean.
Here we independently check its concrete geometric and colouring premises,
including proper full endpoints and an actual retained component switch.
The observer is a graph homomorphism; injectivity and inducedness are not
required by the theorem. No recolouring-history search is used for replay.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_chain_boundary import subdivide
from audit_diamond_sources import read_rows, require
from audit_flat_seven_return import verify as verify_sphere
from audit_independent_repair import complete_patch
from audit_five_triangle_collapse import graph as read_graph
from probe_flat_pairs import geometry, initial_faces

OBSERVER_EDGES = [(0, 1), (1, 2), (2, 0), (0, 3), (1, 4), (2, 5),
                  (0, 6), (1, 7), (2, 8)]
OBSERVER_INITIAL = [0, 2, 1, 1, 0, 2, 3, 3, 3]


def verify_case(here, witness):
    source = here / witness['source_colouring']
    require(sha256(source.read_bytes()).hexdigest() == witness['source_colouring_sha256'],
            'Source colouring pin differs')
    case = json.loads(source.read_text())['cases'][witness['case_index']]
    path = here / case['source_fixture']
    require(sha256(path.read_bytes()).hexdigest() == case['source_fixture_sha256'],
            'Sphere fixture pin differs')
    sphere = verify_sphere(here, path.name)
    fixture = json.loads(path.read_text())
    original = json.loads((here / fixture['source_fixture']).read_text())
    faces = subdivide(initial_faces())
    for a, b, c, d in original['edge_flip_history'][:fixture['edge_flip_prefix']]:
        darts, _, _, _ = geometry(faces)
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d), 'Source flip correspondence differs')
        faces[i], faces[j] = (c, d, b), (d, c, a)
    _, ambient, _, _ = geometry(faces)
    occurrence = fixture['source_occurrence']
    config = here / occurrence['configuration']
    _, ring = read_rows(config.read_text())[0]
    ports = occurrence['images'][:ring]
    removed = set(occurrence['images'][ring:])
    exterior = {v: ns - removed for v, ns in ambient.items() if v not in removed}
    before = {v: c for v, c in enumerate(case['colouring']) if c is not None}
    require({v for v, c in enumerate(case['colouring']) if c is None} == removed,
            'Deleted core differs')
    require(len(case['colouring']) == len(ambient), 'Wrong ambient carrier')
    proper(exterior, before)
    hidden = witness['hidden']
    require(len(hidden) == 2 and len(set(hidden)) == 2 and
            set(hidden) <= exterior.keys() and not set(hidden) & set(ports),
            'Hidden pair must be two actual exterior vertices off the original ports')
    require(hidden[1] in exterior[hidden[0]], 'Hidden vertices are not adjacent')
    retained = {v: ns - set(hidden) for v, ns in exterior.items() if v not in hidden}
    near_before = {v: before[v] for v in retained}
    near_after, support = switch(retained, near_before, witness['pair'], witness['root'])
    protected = set(retained) - support
    after = dict(near_after)
    require(len(witness['target_hidden']) == 2, 'Missing hidden target colours')
    after.update(zip(hidden, witness['target_hidden']))
    proper(exterior, after)
    require(all(after[v] == before[v] for v in protected), 'Endpoint context differs')
    images = witness['observer_images']
    palette = witness['palette']
    require(len(images) == 9 and set(images) <= exterior.keys(), 'Invalid observer carrier')
    require(sorted(palette) == list(range(4)), 'Palette is not a permutation')
    require(all(images[v] in exterior[images[u]] for u, v in OBSERVER_EDGES),
            'Observer does not preserve adjacency')
    require([before[v] for v in images] == [palette[c] for c in OBSERVER_INITIAL],
            'Initial observer colouring differs from the certified frozen state')
    require(set(images[3:]) <= protected, 'An observer boundary vertex can move')
    require(after[images[2]] != palette[1], 'Target does not move the observed core')
    require(images[:2] == hidden, 'Observer core does not match the hidden pair')
    changed_ports = [v for v in ports if after[v] != before[v]]
    require(changed_ports, 'Selected move does not change an original patch port')
    # This is a separate extension question: restoring the original deleted
    # patch is not the same as extending over the newly hidden pair.
    _, patch = read_graph(config.read_bytes())
    initial_extension = complete_patch(patch, [before[v] for v in ports])
    final_extension = complete_patch(patch, [after[v] for v in ports])
    if final_extension is not None:
        ambient_after = dict(after)
        ambient_after.update((occurrence['images'][v], final_extension[v])
                             for v in range(ring, len(final_extension)))
        proper(ambient, ambient_after)
    return {
        'source_colouring': source.name, 'source_case': witness['case_index'],
        'sphere_fixture': path.name, 'configuration': occurrence['configuration'],
        'ambient_vertices': len(ambient), 'exterior_vertices': len(exterior),
        'ambient_degree_range': [min(map(len, ambient.values())), max(map(len, ambient.values()))],
        'exterior_degree_range': [min(map(len, exterior.values())), max(map(len, exterior.values()))],
        'observer_exterior_degrees': [len(exterior[v]) for v in images],
        'observer_images': images, 'observer_distinct_vertices': len(set(images)),
        'observer_is_graph_homomorphism': True,
        'hidden_pair': hidden, 'core_ambient_degrees': [len(ambient[v]) for v in images[:3]],
        'core_exterior_degrees': [len(exterior[v]) for v in images[:3]],
        'retained_component': sorted(support), 'protected_vertices': len(protected),
        'original_patch_ports_changed': changed_ports,
        'both_exterior_endpoints_proper': True,
        'target_extends_over_hidden_pair': True,
        'initial_word_extends_to_original_patch': initial_extension is not None,
        'target_word_extends_to_original_patch': final_extension is not None,
        'fixed_context_lift_obstructed_by_frozen_observer': True,
        'flat_centres': sphere['centres'],
        'obstructing_short_cycles': sphere['obstructing_short_cycles'],
        'concrete_premises_kernel_certified': False,
    }


def verify(here):
    path = here / 'frozen-observer-example.json'
    fixture = json.loads(path.read_text())
    require(len(fixture['cases']) == 2, 'Expected both spherical source cases')
    return {
        'evidence': 'Independent program verification of the actual premises of a kernel-proved observer theorem.',
        'cases': [verify_case(here, case) for case in fixture['cases']],
        'kernel_theorem': 'Mettapedia.GraphTheory.FourColor.FrozenBoundaryObserver.no_lift_renamed',
        'scope': 'Obstructs the specified moves with all unchanged retained vertices protected. '
                 'Does not rule out exterior recolouring with a larger moving context, another command, '
                 'or another decomposition. Ambient degrees are 5..7, but whole-ball flatness and '
                 'minimal-counterexample hypotheses are not asserted.',
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
