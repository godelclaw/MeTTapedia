#!/usr/bin/env python3
"""Replay joint transition guards and physical lifts for hidden adjacent pairs.

Uses the two pinned spherical cases and commands already checked by the frozen
observer and independent repair audits. The new guard rejects the obstructed
commands but reconstructs successful repairs. No history search is performed.
The generic theorem is in Kempe.GuardedLift; these instances are program checks.
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
from audit_frozen_observer import verify as verify_observers
from audit_independent_repair import availability, complete_patch, lifted_step
from probe_flat_pairs import geometry, initial_faces


def guard(adj, hidden, before, after, pair):
    """At most 16 old assignments, each with at most four possible new ones."""
    require(len(hidden) == 2 and len(set(hidden)) == 2 and set(hidden) <= adj.keys(),
            'Invalid hidden pair')
    require(len(pair) == 2 and len(set(pair)) == 2 and set(pair) <= set(range(4)),
            'Invalid colour pair')
    u, v = hidden
    a, b = pair
    keep = set(adj) - set(hidden)
    retained = {x: adj[x] & keep for x in keep}
    proper(retained, {x: before[x] for x in keep})
    proper(retained, {x: after[x] for x in keep})
    def swap(c):
        return b if c == a else a if c == b else c
    require(all(after[x] in (before[x], swap(before[x])) for x in keep),
            'Retained move is not a partial transposition')
    def fits(c, d, state):
        return (v not in adj[u] or c != d) and \
            all(c != state[x] for x in adj[u] & keep) and \
            all(d != state[x] for x in adj[v] & keep)
    for c, d in product(range(4), repeat=2):
        if not fits(c, d, before):
            continue
        for e, f in product(sorted({c, swap(c)}), sorted({d, swap(d)})):
            if fits(e, f, after):
                return [c, d, e, f]
    return None


def realize(adj, hidden, before, after, pair, choice):
    """Prepare, perform the proper partial transposition, then finish."""
    u, v = hidden
    prepared, middle = dict(before), dict(after)
    prepared.update(zip(hidden, choice[:2]))
    middle.update(zip(hidden, choice[2:]))
    proper(adj, prepared)
    proper(adj, middle)
    protected = {x for x in adj if x not in hidden and before[x] == after[x]}
    current, moves = dict(before), []
    def move(colours, root, silent):
        nonlocal current
        target, support = switch(adj, current, colours, root)
        require(not support & protected, 'A protected retained vertex moved')
        if silent:
            require(support <= set(hidden), 'Hidden preparation escaped its fibre')
        moves.append({'pair': list(colours), 'root': root, 'size': len(support),
                      'silent': silent})
        current = target
    def fibre(target):
        require(all(current[x] == target[x] for x in adj if x not in hidden),
                'Different retained fibres')
        if current[v] != target[u]:
            order = [u, v]
        elif current[u] != target[v]:
            order = [v, u]
        else:
            order = []
            if current != target:
                move([current[u], current[v]], u, True)
        for x in order:
            if current[x] != target[x]:
                move([current[x], target[x]], x, True)
        require(current == target, 'Two-vertex fibre reconstruction failed')
    fibre(prepared)
    while current != middle:
        changed = {x for x in adj if current[x] != middle[x]}
        root = min(changed)
        move(pair, root, False)
        require({x for x in adj if current[x] != middle[x]} < changed,
                'Joint realization did not strictly advance')
    fibre(after)
    return moves


def verify(here):
    observed = verify_observers(here)
    witnesses = json.loads((here / 'frozen-observer-example.json').read_text())['cases']
    sources = json.loads((here / 'independent-repair-example.json').read_text())['cases']
    records = []
    for index, (case, witness) in enumerate(zip(sources, witnesses)):
        require(witness['source_colouring'] == 'independent-repair-example.json' and
                witness['case_index'] == index, 'Observer uses another source colouring')
        fixture = json.loads((here / case['source_fixture']).read_text())
        original = json.loads((here / fixture['source_fixture']).read_text())
        faces = subdivide(initial_faces())
        for a, b, c, d in original['edge_flip_history'][:fixture['edge_flip_prefix']]:
            darts, _, _, _ = geometry(faces)
            i, ac = darts[a, b]
            j, ad = darts[b, a]
            require((ac, ad) == (c, d), 'Source flip differs')
            faces[i], faces[j] = (c, d, b), (d, c, a)
        _, ambient, _, _ = geometry(faces)
        occurrence = fixture['source_occurrence']
        ring, patch = graph((here / occurrence['configuration']).read_bytes())
        ports = occurrence['images'][:ring]
        removed = set(occurrence['images'][ring:])
        adj = {v: ws - removed for v, ws in ambient.items() if v not in removed}
        initial = {v: c for v, c in enumerate(case['colouring']) if c is not None}
        proper(adj, initial)
        hidden = witness['hidden']
        retained = {v: ws - set(hidden) for v, ws in adj.items() if v not in hidden}
        bad, _ = switch(retained, {v: initial[v] for v in retained},
                        witness['pair'], witness['root'])
        require(guard(adj, hidden, initial, bad, witness['pair']) is None,
                'Transition guard accepted the frozen command')
        # Deliberately forgetting the hidden edge makes the two marginal
        # colour choices look compatible. This is an exact negative control.
        cut = {x: set(ns) for x, ns in adj.items()}
        u, v = hidden
        cut[u].remove(v)
        cut[v].remove(u)
        require(guard(cut, hidden, initial, bad, witness['pair']) is not None,
                'Expected the internal-edge constraint to be essential')
        current = dict(initial)
        independent = set(case['hidden'])
        small_graph = {v: ws - independent for v, ws in adj.items() if v not in independent}
        transitions = []
        for command in case['commands']:
            pair = command['pair']
            a, b = pair
            small = {v: current[v] for v in small_graph}
            chosen = set()
            for root in command['roots']:
                _, support = switch(small_graph, small, pair, root)
                require(not chosen & support, 'Component chosen twice')
                chosen |= support
            target = {v: (b if c == a else a) if v in chosen else c for v, c in small.items()}
            choices = availability(adj, independent, target)
            require(all(choices.values()), 'Original successful command no longer extends')
            after = dict(target)
            for v, allowed in choices.items():
                after[v] = current[v] if current[v] in allowed else min(allowed)
            for phase in lifted_step(adj, independent, current, after, pair):
                for old_move in phase['switches']:
                    next_state, support = switch(adj, current, old_move['pair'], old_move['root'])
                    choice = guard(adj, hidden, current, next_state, old_move['pair'])
                    require(choice is not None, 'Guard rejected an actual physical move')
                    moves = realize(adj, hidden, current, next_state, old_move['pair'], choice)
                    transitions.append({'pair': old_move['pair'], 'hidden_choices': choice,
                                        'retained_vertices_changed': len(support - set(hidden)),
                                        'reconstructed_moves': moves})
                    current = next_state
            require(current == after, 'Physical reconstruction changed the endpoint')
        completion = complete_patch(patch, [current[v] for v in ports])
        require(completion is not None, 'Original patch no longer reconstructs')
        whole = dict(current)
        whole.update((occurrence['images'][i], completion[i]) for i in range(ring, len(completion)))
        proper(ambient, whole)
        records.append({'configuration': occurrence['configuration'], 'hidden_pair': hidden,
                        'ambient_vertices': len(ambient), 'retained_exterior_vertices': len(retained),
                        'guard_neighbours': len((adj[hidden[0]] | adj[hidden[1]]) - set(hidden)),
                        'blocked_command_rejected': True, 'dropping_hidden_edge_admits_bad_move': True,
                        'successful_guarded_transitions': transitions,
                        'full_sphere_reconstructed': True})
    return {'evidence': 'Independent program replay of guards and reconstructed physical histories.',
            'cases': records, 'observer_cases_replayed': len(observed['cases']),
            'generic_lean_theorem': 'SimpleGraph.KempeGuardedLift.two_vertex_history_iff',
            'scope': 'Two concrete exteriors. The generic guard theorem is kernel proved; these graph '
                     'instances and their geometry are program checked. No recognition, coverage, '
                     'strict ordinary graph reduction or catalogue saving is claimed.',
            'source_sha256': {name: sha256((here / name).read_bytes()).hexdigest()
                              for name in ['frozen-observer-example.json', 'independent-repair-example.json']},
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
