#!/usr/bin/env python3
"""Replay a path-joining preparation and a counterexample to its local guard.

The general two-step supplier and whole-map reconstruction are checked in
Lean. This program checks the concrete sphere representations and commands,
including larger exteriors generated without changing the source core.
It does not search for successful commands or assert universal repair supply.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_component_detach import data, PAIRS
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_odd_mesh import refine
from audit_two_port_core import eliminate
from probe_flat_pairs import geometry


def verify(here):
    fixture_path = here / 'residual-port-preparation-example.json'
    fixture = json.loads(fixture_path.read_text())
    base_path = here / fixture['source_fixture']
    require(sha256(base_path.read_bytes()).hexdigest() == fixture['source_fixture_sha256'],
            'Source fixture pin differs')
    base, ambient, exterior, ports, initial, *_ = data(here)
    require(fixture['source_fixture'] == 'component-detach-example.json', 'Wrong base fixture')
    ring, patch = graph((here / base['configuration']).read_bytes())
    core = set(base['images'][ring:])
    inside = [tuple(f) for f in base['faces'] if core.intersection(f)]
    outside = [tuple(f) for f in base['faces'] if not core.intersection(f)]
    _, _, rotations, _ = geometry(base['faces'])
    word = [initial[v] for v in ports]
    require(word == [1,3,2,3,1,0,3,0,2,0,2], 'Wrong boundary class')
    source_assignment = fixture['source_assignment']
    proper(dict(enumerate(patch)), dict(enumerate(source_assignment)))
    require(source_assignment == [1,3,1,3,1,0,3,2,0,2,0,1,2,1,3,0,3,2],
            'Source assignment differs from the theorem')

    def inspect(faces, colours, guarded):
        _, whole, turn, _ = geometry(faces)
        require(all(whole[v] == ambient[v] for v in core), 'A source core star changed')
        require(all(turn[v,u] == rotations[v,u] for v in core for u in ambient[v]),
                'Cyclic core order changed')
        remaining = {v: ns-core for v,ns in whole.items() if v not in core}
        proper(remaining, colours)
        require([colours[v] for v in ports] == word, 'Boundary colours changed')
        component13 = next(b for b in components(remaining, colours, (1,3)) if ports[6] in b)
        require(ports[3] in component13 and ports[1] not in component13,
                'Input is outside the residual connectivity case')
        neighbours = sorted(v for v in remaining[ports[2]] if colours[v] == 1)
        require(bool(neighbours) != guarded, 'Local free-port condition differs')
        # Complete one-step census: silent components cannot change extension.
        component_count = 0
        accepted = 0
        for pair in PAIRS:
            for block in components(remaining, colours, pair):
                component_count += 1
                after_word = [colours[v] ^ pair[0] ^ pair[1] if v in block else colours[v]
                              for v in ports]
                accepted += eliminate(patch, ring, after_word)[0] is not None
        require(accepted == 0, 'Input has a one-step repair')
        prepared, first = switch(remaining, colours, fixture['prepare_pair'],
                                 ports[fixture['prepare_port']])
        require(first.intersection(ports) == {ports[2]}, 'First boundary observation differs')
        if guarded:
            require(first == {ports[2]}, 'Free port is not a singleton component')
        require([prepared[v] for v in ports] == [1,3,1,3,1,0,3,0,2,0,2],
                'Prepared boundary differs')
        path_component = next(b for b in components(remaining, prepared, (1,3)) if ports[1] in b)
        require(ports[6] in path_component, 'Preparation did not join the complementary paths')
        repaired, second = switch(remaining, prepared, fixture['finish_pair'],
                                  ports[fixture['finish_port']])
        require([i for i,v in enumerate(ports) if v in second] == [7,8,9,10],
                'Final boundary component differs')
        require([repaired[v] for v in ports] == source_assignment[:ring],
                'Repaired exterior disagrees with source assignment')
        completed = repaired | {base['images'][v]:source_assignment[v] for v in range(ring,len(patch))}
        proper(whole, completed)
        return {'vertices':len(whole), 'exterior_vertices':len(remaining), 'faces':len(faces),
                'minimum_degree':min(map(len,whole.values())), 'residual_connectivity':True,
                'core_adjacency_and_cyclic_order_preserved':True,
                'all_initial_components':component_count, 'one_switch_repairs':accepted,
                'colour_one_neighbours_of_port_two':neighbours,
                'component_sizes':[len(first),len(second)],
                'changed_ports':[[2],[7,8,9,10]], 'whole_colouring_reconstructed':True}

    rows = []
    for width in fixture['widths']:
        if width == 1:
            faces, colours = base['faces'], initial
        else:
            refined, colours, _, _ = refine(outside, initial, max(ambient)+1, width)
            faces = inside + refined
        row = inspect(faces, colours, True)
        row['mesh_width'] = width
        row['short_cycle_census'] = 'retained base checked by data()' if width == 1 else 'not performed'
        rows.append(row)
    blocked = {v:c for v,c in enumerate(fixture['blocked_colour']) if c is not None}
    obstruction = inspect(base['faces'], blocked, False)
    require(obstruction['colour_one_neighbours_of_port_two'] == fixture['blocked_neighbours'],
            'Guard obstruction changed')
    return {'evidence':'Exact program replay; geometric instances are separate from the parameterized Lean theorem.',
            'fixture_sha256':sha256(fixture_path.read_bytes()).hexdigest(),
            'source_fixture_sha256':fixture['source_fixture_sha256'], 'guarded_cases':rows,
            'guard_counterexample':obstruction,
            'scope':'No immediate repair succeeds on these inputs. The free-port supplier applies to the guarded cases. '
                    'The counterexample refutes universal availability of that local guard; its two-vertex preparation '
                    'also succeeds, but is not covered by the free-port theorem. Larger meshes are checked oriented '
                    'triangulated spheres with preserved core stars, without a new short-cycle census.',
            'catalogue_entries_removed':0, 'original_certificates_removed':0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
