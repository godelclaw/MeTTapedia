#!/usr/bin/env python3
"""Replay both orders of the separated-component radius-three repair.

The execution uses actual connected components of the entire punctured
exterior. No Kempe history search is rerun. Lean proves the generic commutation
law and this literal reconstruction; geometry remains program evidence.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_boundary_observation import proper, switch
from audit_diamond_sources import require
from audit_flat_seven_return import verify as verify_sphere
from audit_forest_repair import load_case
from audit_two_port_core import eliminate


def verify(here):
    path = here / 'local-repair-history-example.json'
    fixture = json.loads(path.read_text())
    start_path = here / fixture['starting_fixture']
    require(sha256(start_path.read_bytes()).hexdigest() == fixture['starting_fixture_sha256'],
            'Starting fixture differs')
    start = json.loads(start_path.read_text())
    source_path = here / start['source_fixture']
    require(sha256(source_path.read_bytes()).hexdigest() == start['source_fixture_sha256'],
            'Source geometry differs')
    geometry = verify_sphere(here, source_path.name)
    seed = json.loads((here / 'independent-repair-example.json').read_text())['cases'][0]
    require(seed['source_fixture'] == start['source_fixture'], 'Source reader differs')
    ambient, adj, occurrence, ring, patch, ports, _ = load_case(here, seed)
    core = set(ambient) - set(adj)
    core_colours = dict(fixture['core_colours'])
    require(set(core_colours) == core, 'Wrong reconstructed core')
    initial = {v: c for v, c in enumerate(start['initial']) if c is not None}
    proper(adj, initial)
    require(eliminate(patch, ring, tuple(initial[v] for v in ports))[0] is None,
            'Starting boundary already extends')
    balls = [core]
    for _ in range(3):
        balls.append(balls[-1] | set().union(*(ambient[v] for v in balls[-1])))

    commands = fixture['commands']
    require(len(commands) == 2, 'Expected two separated commands')
    supports = [set(cmd['chain']) for cmd in commands]
    require(not supports[0] & supports[1], 'Supports intersect')
    require(not any(adj[v] & supports[1] for v in supports[0]), 'Supports have a connecting edge')
    for cmd, support in zip(commands, supports):
        require(cmd['root'] in support and all(v in adj[w] for v, w in zip(cmd['chain'], cmd['chain'][1:])),
                'The chain is disconnected or misses its root')
        _, actual = switch(adj, initial, cmd['pair'], cmd['root'])
        require(actual == support, 'The chain is not the complete initial component')
        require(support <= balls[3], 'A support leaves radius three')
    endpoints, histories = [], []
    for order in [(0, 1), (1, 0)]:
        current = dict(initial)
        history = []
        for i in order:
            cmd = commands[i]
            current, actual = switch(adj, current, cmd['pair'], cmd['root'])
            require(actual == supports[i], 'The first switch changed the second component')
            require(all(current[v] == initial[v] for v in adj if v not in balls[3]),
                    'An intermediate state changed the farther exterior')
            history.append({'pair': cmd['pair'], 'root': cmd['root'], 'support': sorted(actual)})
        full = current | core_colours
        proper(ambient, full)
        require(any(full[v] != initial[v] for v in adj if v not in balls[2]),
                'The reconstruction did not need the third shell')
        endpoints.append(full)
        histories.append(history)
    require(endpoints[0] == endpoints[1], 'The two orders disagree')

    lean_root = here.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory'
    consumer = lean_root / 'FourColor/LocalRepairHistory.lean'
    generic = lean_root / 'Kempe/SeparatedChains.lean'
    text = consumer.read_text()
    for name, cmd in zip(['firstChain', 'secondChain'], commands):
        declaration = re.search(r'def ' + name + r' : List E := (\[.*?\])', text, re.S)[1]
        require(list(map(int, re.findall(r'⟨(\d+),', declaration))) == cmd['chain'],
                'The Lean chain differs: ' + name)
    return {
        'classification': 'CHECKED_TWO_ORDER_PHYSICAL_RECONSTRUCTION',
        'vertices': len(ambient), 'exterior_vertices': len(adj), 'restored_vertices': len(core),
        'ball_sizes': list(map(len, balls)), 'histories': histories,
        'same_full_endpoint': True, 'physical_steps_in_each_history': 2,
        'intermediate_states_fixed_outside_radius_three': True,
        'reconstruction_changes_radius_three_shell': True,
        'source_geometry': {'centre_charges': geometry['charges'],
                            'short_cycles_checked': geometry['short_cycles_checked'],
                            'kernel_certified': False},
        'lean': {'generic_law': 'KempeSeparatedChains.Certificate.commute',
                 'consumer': 'LocalRepairHistory.reconstruction',
                 'locality': 'LocalRepairHistory.both_orders_fixed'},
        'pins': {p.name: sha256(p.read_bytes()).hexdigest() for p in [path, start_path, consumer, generic]},
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'limits': ['The supplied colouring and occurrence are fixed; no universal radius-three repair theorem.',
                   'No uniform occurrence supply, whole-ball flatness, or minimal-counterexample classification.',
                   'Separation of the two supports is a proved hypothesis, not a property of arbitrary repairs.',
                   'No catalogue dependency removal or complete-proof cost saving.']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end='')
