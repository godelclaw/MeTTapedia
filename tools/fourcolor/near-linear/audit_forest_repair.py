#!/usr/bin/env python3
"""Replay forest guard elimination and physical reconstruction in two spheres.

Eight local labels encode an old colour and a switch bit. Leaf messages
retain exact joint choices; no product of forest colourings is enumerated.
The generic laws are Lean checked. Concrete source geometry and executions
in this script remain independently checked program evidence.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_chain_boundary import subdivide
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import availability, complete_patch, lifted_step
from audit_transition_guard import verify as verify_pairs
from probe_flat_pairs import geometry, initial_faces


def load_case(here, case):
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
    ports, removed = occurrence['images'][:ring], set(occurrence['images'][ring:])
    adj = {x: ns - removed for x, ns in ambient.items() if x not in removed}
    initial = {v: c for v, c in enumerate(case['colouring']) if c is not None}
    proper(adj, initial)
    return ambient, adj, occurrence, ring, patch, ports, initial


def forest_order(adj, hidden):
    require(set(hidden) <= adj.keys(), 'Foreign hidden vertex')
    active = set(hidden)
    order = []
    while active:
        leaves = [x for x in active if len(adj[x] & active) <= 1]
        require(leaves, 'Hidden graph contains a cycle')
        v = min(leaves)
        neighbours = adj[v] & active
        order.append((v, next(iter(neighbours)) if neighbours else None))
        active.remove(v)
    return order


def forest_guard(adj, hidden, before, after, pair):
    order = forest_order(adj, hidden)
    a, b = pair
    def target(s):
        c, bit = s
        return (b if c == a else a if c == b else c) if bit else c
    def compatible(s, t):
        return s[0] != t[0] and target(s) != target(t)
    labels = [(c, bit) for c in range(4) for bit in (False, True)]
    domains = {x: [s for s in labels if all(s[0] != before[y] and target(s) != after[y]
                for y in adj[x] - hidden)] for x in hidden}
    snapshots = {}
    tests = 0
    for v, parent in order:
        snapshots[v] = domains[v][:]
        if not domains[v]:
            return None, {'forward_edge_comparisons': tests, 'failure_vertex': v}
        if parent is not None:
            kept = []
            for t in domains[parent]:
                for s in domains[v]:
                    tests += 1
                    if compatible(s, t):
                        kept.append(t)
                        break
            domains[parent] = kept
    assignment = {}
    for v, parent in reversed(order):
        assignment[v] = next(s for s in snapshots[v]
                             if parent is None or compatible(s, assignment[parent]))
    old = {x: s[0] for x, s in assignment.items()}
    new = {x: target(s) for x, s in assignment.items()}
    require(all(compatible(assignment[x], assignment[y]) for x in hidden for y in adj[x] & hidden),
            'Leaf reconstruction lost an internal edge')
    return (old, new), {'forward_edge_comparisons': tests, 'max_local_labels': 8,
                        'leaf_messages': sum(parent is not None for _, parent in order)}


def list_path(adj, allowed, initial, final):
    """Construct the leaf-induction path, retaining all vertex lists."""
    require(set(adj) == set(initial) == set(final) == set(allowed), 'List carrier differs')
    proper(adj, initial)
    proper(adj, final)
    require(all(initial[x] in allowed[x] and final[x] in allowed[x] for x in adj),
            'A fibre endpoint violates its list')
    if initial == final:
        return []
    v, _ = forest_order(adj, set(adj))[0]
    rest = {x: ns - {v} for x, ns in adj.items() if x != v}
    lists = {x: set(cs) for x, cs in allowed.items() if x != v}
    c, d = initial[v], final[v]
    if c == d:
        for x in adj[v]:
            lists[x].discard(c)
    small = list_path(rest, lists, {x: initial[x] for x in rest}, {x: final[x] for x in rest})
    def extend(state):
        z = next(z for z in (c, d) if all(z != state[x] for x in adj[v]))
        return dict(state) | {v: z}
    current = dict(initial)
    result = []
    def append(pair, target):
        nonlocal current
        if current == target:
            return
        a, b = pair
        swap = lambda c: b if c == a else a if c == b else c
        require(all(target[x] in (current[x], swap(current[x])) for x in adj), 'Not one pair move')
        proper(adj, target)
        require(all(target[x] in allowed[x] for x in adj), 'A list was lost during lifting')
        result.append((list(pair), dict(target)))
        require(len(result) <= 20000, 'Bounded execution test exceeded its step limit')
        current = target
    first = extend({x: initial[x] for x in rest})
    append((current[v], first[v]), first)
    for pair, small_target in small:
        target = extend(small_target)
        a, b = pair
        swap = lambda c: b if c == a else a if c == b else c
        choices = sorted({current[v], target[v]})
        bridges = [(z, z2) for z in choices for z2 in choices
                   if z2 in (z, swap(z)) and all(z != current[x] for x in adj[v])
                   and all(z2 != target[x] for x in adj[v])]
        require(bridges, 'Single-vertex colour bridge failed')
        z, z2 = bridges[0]
        append((current[v], z), current | {v: z})
        append(pair, target | {v: z2})
        append((z2, target[v]), target)
    append((current[v], final[v]), dict(final))
    require(current == final, 'Leaf reconstruction missed its endpoint')
    return result


def realize(adj, hidden, initial, final, pair, choices):
    prepared, middle = dict(initial), dict(final)
    prepared.update(choices[0])
    middle.update(choices[1])
    proper(adj, prepared)
    proper(adj, middle)
    current = dict(initial)
    protected = {x for x in adj if x not in hidden and initial[x] == final[x]}
    counts = {'prepare': 0, 'joint': 0, 'finish': 0}
    largest = 0
    def partial(pair, target, phase, silent=False):
        nonlocal current, largest
        proper(adj, target)
        while current != target:
            changed = {x for x in adj if current[x] != target[x]}
            next_state, support = switch(adj, current, pair, min(changed))
            require(not support & protected, 'A protected vertex moved')
            require(not silent or support <= hidden, 'A fibre switch escaped the hidden set')
            require({x for x in adj if next_state[x] != target[x]} < changed,
                    'Physical realization did not strictly advance')
            current = next_state
            counts[phase] += 1
            largest = max(largest, len(support))
    def fibre(target, phase):
        allowed = {x: set(range(4)) - {current[y] for y in adj[x] - hidden}
                   for x in hidden}
        forest = {x: adj[x] & hidden for x in hidden}
        path = list_path(forest, allowed, {x: current[x] for x in hidden},
                         {x: target[x] for x in hidden})
        for colours, state in path:
            partial(colours, current | state, phase, silent=True)
        require(current == target, 'Fibre endpoint differs')
    fibre(prepared, 'prepare')
    partial(pair, middle, 'joint')
    fibre(final, 'finish')
    return {'switches_by_phase': counts, 'largest_component': largest}


def verify(here):
    prior = verify_pairs(here)
    path = here / 'forest-repair-example.json'
    fixture = json.loads(path.read_text())
    source = here / fixture['source']
    require(sha256(source.read_bytes()).hexdigest() == fixture['source_sha256'], 'Source pin differs')
    observers = json.loads(source.read_text())['cases']
    sources = json.loads((here / 'independent-repair-example.json').read_text())['cases']
    require(len(fixture['cases']) == len(observers) == len(sources) == 2, 'Expected two cases')
    records = []
    for selected, observer, case in zip(fixture['cases'], observers, sources):
        ambient, adj, occurrence, ring, patch, ports, initial = load_case(here, case)
        require(selected['configuration'] == occurrence['configuration'], 'Wrong source')
        hidden = set(selected['hidden'])
        require(len(hidden) == len(selected['hidden']), 'Repeated hidden vertex')
        order = forest_order(adj, hidden)
        require(set(observer['hidden']) <= hidden, 'Lost the interacting pair')
        require(not hidden & (set(ports) | set(observer['observer_images'][3:])),
                'A patch port or protected observer leaf was hidden')
        small_graph = {x: ns - set(observer['hidden']) for x, ns in adj.items()
                       if x not in observer['hidden']}
        bad, _ = switch(small_graph, {x: initial[x] for x in small_graph}, observer['pair'], observer['root'])
        bad.update(zip(observer['hidden'], observer['target_hidden']))
        proper(adj, bad)
        rejected, bad_cost = forest_guard(adj, hidden, initial, bad, observer['pair'])
        require(rejected is None, 'The joint guard lost the frozen obstruction')
        independent = set(case['hidden'])
        near = {x: ns - independent for x, ns in adj.items() if x not in independent}
        current = dict(initial)
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
            after = {x: (b if c == a else a) if x in chosen else c for x, c in small.items()}
            allowed = availability(adj, independent, after)
            require(all(allowed.values()), 'Source command does not extend')
            for x, colours in allowed.items():
                after[x] = current[x] if current[x] in colours else min(colours)
            for phase in lifted_step(adj, independent, current, after, pair):
                for move in phase['switches']:
                    next_state, _ = switch(adj, current, move['pair'], move['root'])
                    choices, cost = forest_guard(adj, hidden, current, next_state, move['pair'])
                    require(choices is not None, 'A physical move failed the exact guard')
                    cost.update(realize(adj, hidden, current, next_state, move['pair'], choices))
                    transitions.append(cost)
                    current = next_state
            require(current == after, 'Source repair endpoint differs')
        completion = complete_patch(patch, [current[x] for x in ports])
        require(completion is not None, 'Original patch does not reconstruct')
        whole = dict(current)
        whole.update((occurrence['images'][i], completion[i]) for i in range(ring, len(completion)))
        proper(ambient, whole)
        edges = sum(len(adj[x] & hidden) for x in hidden) // 2
        records.append({'configuration': occurrence['configuration'], 'ambient_vertices': len(ambient),
                        'exterior_vertices': len(adj), 'hidden_vertices': len(hidden),
                        'retained_vertices': len(adj) - len(hidden), 'forest_edges': edges,
                        'forest_components': len(hidden) - edges,
                        'max_hidden_degree': max(len(adj[x] & hidden) for x in hidden),
                        'cross_interface_edges': sum(len(adj[x] - hidden) for x in hidden),
                        'eight_state_labels_per_vertex': True, 'peeling_steps': len(order),
                        'rejected_command': bad_cost, 'successful_transitions': transitions,
                        'full_sphere_reconstructed': True})
    return {'evidence': 'Independent replay of exact leaf guards and actual component switches.',
            'cases': records, 'prior_pair_consumers_replayed': len(prior['cases']),
            'kernel_theorems': ['SimpleGraph.KempeForestFibre.history_iff',
                               'SimpleGraph.KempeForestGuard.peel_transition_iff'],
            'scope': 'An induced forest has no hidden physical-class obstruction. Exact guards remain '
                     'constraints on a shared exterior, not ordinary graph edges. No repeated arbitrary '
                     'elimination, global coverage, catalogue reduction or near-linear physical history '
                     'bound is asserted. Concrete instances are program checked, not kernel certified.',
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
