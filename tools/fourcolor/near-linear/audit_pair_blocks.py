#!/usr/bin/env python3
"""Replay simultaneous guarded deletion of singleton and edge blocks.

All guards share one retained colouring and colour transposition. Witnesses
are chosen locally per hidden block, then assembled and realized as actual
full-graph Kempe histories. No product of block state tables is enumerated.
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
from audit_independent_repair import availability, complete_patch, lifted_step
from audit_transition_guard import verify as verify_pairs
from probe_flat_pairs import geometry, initial_faces


def validate_blocks(adj, blocks):
    flat = [x for block in blocks for x in block]
    hidden = set(flat)
    require(len(flat) == len(hidden) and hidden <= adj.keys(), 'Blocks overlap or contain foreign vertices')
    require(all(1 <= len(block) <= 2 for block in blocks), 'A block exceeds two vertices')
    require(all(adj[x] & hidden <= set(block) for block in blocks for x in block),
            'An edge crosses two hidden blocks')
    return hidden


def local_guard(adj, hidden, block, before, after, pair):
    a, b = pair
    def swap(c):
        return b if c == a else a if c == b else c
    def fits(values, state):
        colours = dict(zip(block, values))
        return all(colours[x] != colours[y] for x in block for y in adj[x] & set(block)) and \
            all(colours[x] != state[y] for x in block for y in adj[x] - hidden)
    for old in product(range(4), repeat=len(block)):
        if not fits(old, before):
            continue
        for new in product(*(sorted({c, swap(c)}) for c in old)):
            if fits(new, after):
                return [list(old), list(new)]
    return None


def realize(adj, blocks, before, after, pair, choices):
    hidden = validate_blocks(adj, blocks)
    prepared, middle = dict(before), dict(after)
    for block, (old, new) in zip(blocks, choices):
        prepared.update(zip(block, old))
        middle.update(zip(block, new))
    proper(adj, prepared)
    proper(adj, middle)
    current = dict(before)
    protected = {x for x in adj if x not in hidden and before[x] == after[x]}
    counts = {'prepare': 0, 'joint': 0, 'finish': 0}
    largest = 0
    def move(colours, root, phase, block=None):
        nonlocal current, largest
        current, support = switch(adj, current, colours, root)
        require(not support & protected, 'A protected retained vertex moved')
        if block is not None:
            require(support <= set(block), 'Silent repair escaped its own block')
        counts[phase] += 1
        largest = max(largest, len(support))
    def fibres(target, phase):
        for block in blocks:
            u, v = block[0], block[-1]
            if current[v] != target[u]:
                order = [u, v]
            elif current[u] != target[v]:
                order = [v, u]
            else:
                order = []
                if any(current[x] != target[x] for x in block):
                    move([current[u], current[v]], u, phase, block)
            for x in order:
                if current[x] != target[x]:
                    move([current[x], target[x]], x, phase, block)
        require(current == target, 'Fibre reconstruction failed')
    fibres(prepared, 'prepare')
    while current != middle:
        changed = {x for x in adj if current[x] != middle[x]}
        move(pair, min(changed), 'joint')
        require({x for x in adj if current[x] != middle[x]} < changed,
                'Joint realization did not strictly advance')
    fibres(after, 'finish')
    return {'switches_by_phase': counts, 'largest_component': largest}


def verify(here):
    previous = verify_pairs(here)
    path = here / 'pair-blocks-example.json'
    selected = json.loads(path.read_text())
    require(sha256((here / selected['source']).read_bytes()).hexdigest() == selected['source_sha256'],
            'Source pin differs')
    observers = json.loads((here / selected['source']).read_text())['cases']
    sources = json.loads((here / 'independent-repair-example.json').read_text())['cases']
    require(len(selected['cases']) == len(observers) == len(sources) == 2, 'Expected both source cases')
    records = []
    for case, observer, selection in zip(sources, observers, selected['cases']):
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
        require(selection['configuration'] == occurrence['configuration'], 'Wrong configuration')
        ring, patch = graph((here / occurrence['configuration']).read_bytes())
        ports, removed = occurrence['images'][:ring], set(occurrence['images'][ring:])
        adj = {x: ns - removed for x, ns in ambient.items() if x not in removed}
        blocks = selection['blocks']
        hidden = validate_blocks(adj, blocks)
        require(not hidden & (set(ports) | set(observer['observer_images'][3:])),
                'A reconstruction port or protected observer leaf was removed')
        require(observer['hidden'] in blocks, 'The interacting obstruction pair is absent')
        initial = {v: c for v, c in enumerate(case['colouring']) if c is not None}
        pair_hidden = set(observer['hidden'])
        pair_graph = {x: ns - pair_hidden for x, ns in adj.items() if x not in pair_hidden}
        bad, _ = switch(pair_graph, {x: initial[x] for x in pair_graph}, observer['pair'], observer['root'])
        bad.update(zip(observer['hidden'], observer['target_hidden']))
        proper(adj, bad)
        rejected = [block for block in blocks
                    if local_guard(adj, hidden, block, initial, bad, observer['pair']) is None]
        require(observer['hidden'] in rejected, 'Additional elimination lost the observer obstruction')
        current = dict(initial)
        independent = set(case['hidden'])
        near = {x: ns - independent for x, ns in adj.items() if x not in independent}
        transitions = []
        for command in case['commands']:
            pair = command['pair']
            a, b = pair
            small = {x: current[x] for x in near}
            chosen = set()
            for root in command['roots']:
                _, support = switch(near, small, pair, root)
                require(not chosen & support, 'Component chosen twice')
                chosen |= support
            target = {x: (b if c == a else a) if x in chosen else c for x, c in small.items()}
            allowed = availability(adj, independent, target)
            require(all(allowed.values()), 'Source command does not extend')
            after = dict(target)
            for x, colours in allowed.items():
                after[x] = current[x] if current[x] in colours else min(colours)
            for phase in lifted_step(adj, independent, current, after, pair):
                for source_move in phase['switches']:
                    next_state, _ = switch(adj, current, source_move['pair'], source_move['root'])
                    choices = [local_guard(adj, hidden, block, current, next_state, source_move['pair'])
                               for block in blocks]
                    require(all(c is not None for c in choices), 'A local guard rejected a physical step')
                    transitions.append(realize(adj, blocks, current, next_state, source_move['pair'], choices))
                    current = next_state
            require(current == after, 'Endpoint changed during replay')
        completion = complete_patch(patch, [current[x] for x in ports])
        require(completion is not None, 'Original patch does not reconstruct')
        whole = dict(current)
        whole.update((occurrence['images'][i], completion[i]) for i in range(ring, len(completion)))
        proper(ambient, whole)
        widths = [len(set().union(*(adj[x] for x in block)) - hidden) for block in blocks]
        records.append({'configuration': occurrence['configuration'], 'ambient_vertices': len(ambient),
                        'exterior_vertices': len(adj), 'hidden_vertices': len(hidden),
                        'retained_vertices': len(adj) - len(hidden), 'pair_blocks': sum(len(b) == 2 for b in blocks),
                        'singleton_blocks': sum(len(b) == 1 for b in blocks), 'guards': len(blocks),
                        'guard_neighbour_widths': widths, 'guard_neighbour_incidences': sum(widths),
                        'previous_independent_hidden_vertices': len(independent),
                        'previous_availability_neighbour_incidences': sum(len(adj[x]) for x in independent),
                        'rejected_blocks_for_obstructed_command': rejected,
                        'successful_transitions': transitions, 'full_sphere_reconstructed': True})
    return {'evidence': 'Independent program replay of factored guards and full physical reconstruction.',
            'cases': records, 'prior_pair_consumers_replayed': len(previous['cases']),
            'generic_lean_theorem': 'SimpleGraph.KempePairBlocks.history_iff',
            'scope': 'A constrained transition representation, not an ordinary smaller-graph reduction. '
                     'Concrete geometry remains program evidence. No repeated-elimination closure, '
                     'geometric coverage or catalogue saving is asserted.',
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
