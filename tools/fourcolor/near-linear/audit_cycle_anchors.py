#!/usr/bin/env python3
"""Replay exact anchor transitions and physical reconstruction in a sphere.

Feasibility and transitions use forest leaf guards. The separate tiny-case
cross-check enumerates at most seven cycle vertices and compares their actual
component switches; it is not part of the generic Lean proof.
"""
import argparse
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_diamond_sources import require
from audit_forest_repair import forest_guard, load_case, realize
from audit_independent_repair import availability, complete_patch, verify_case


def whole_case(here, case):
    ambient, adj, occ, ring, patch, ports, current = load_case(here, case)
    hidden = set(case['hidden'])
    near = {x: ns - hidden for x, ns in adj.items() if x not in hidden}
    for command in case['commands']:
        a, b = command['pair']
        small = {x: current[x] for x in near}
        chosen = set()
        for root in command['roots']:
            _, support = switch(near, small, (a, b), root)
            require(not chosen & support, 'Repeated component')
            chosen |= support
        after = {x: (b if c == a else a) if x in chosen else c for x, c in small.items()}
        allowed = availability(adj, hidden, after)
        require(all(allowed.values()), 'No extension')
        after.update((x, current[x] if current[x] in cs else min(cs)) for x, cs in allowed.items())
        proper(adj, after)
        current = after
    completion = complete_patch(patch, [current[x] for x in ports])
    require(completion is not None, 'No completion')
    current.update((occ['images'][i], completion[i]) for i in range(ring, len(completion)))
    proper(ambient, current)
    return ambient, current


def connected_components(adj):
    remaining = set(adj)
    result = []
    while remaining:
        root = min(remaining)
        todo, seen = [root], {root}
        while todo:
            x = todo.pop()
            more = adj[x] - seen
            seen |= more
            todo.extend(more)
        remaining -= seen
        result.append(sorted(seen))
    return result


def analyse(adj, current, cycle, anchor, check=False):
    S = set(cycle)
    H = S - {anchor}
    witnesses = {}
    retained = {x: current[x] for x in adj if x not in H}
    for c in range(4):
        word = retained | {anchor: c}
        if any(word[x] == word[y] for x in word for y in adj[x] & word.keys()):
            continue
        feasible, _ = forest_guard(adj, H, word, word, (0, 0))
        if feasible is not None:
            witnesses[c] = word | feasible[0]
            proper(adj, witnesses[c])
    graph = {c: set() for c in witnesses}
    costs = []
    for c, d in combinations(witnesses, 2):
        choices, cost = forest_guard(adj, H, witnesses[c], witnesses[d], (c, d))
        if choices is not None:
            graph[c].add(d)
            graph[d].add(c)
            if check:
                cost.update(realize(adj, H, witnesses[c], witnesses[d], (c, d), choices))
            costs.append({'pair': [c, d], **cost})
    record = {'cycle': cycle, 'anchor': anchor, 'feasible': sorted(witnesses),
              'classes': connected_components(graph), 'transitions': costs}
    if check:
        allowed = [set(range(4)) - {current[y] for y in adj[x] - S} for x in cycle]
        states = {cs: current | dict(zip(cycle, cs)) for cs in product(*map(sorted, allowed))
                  if all(cs[i] != cs[j] for i in range(len(cycle)) for j in range(i)
                         if cycle[j] in adj[cycle[i]])}
        physical = {cs: set() for cs in states}
        for cs, state in states.items():
            for pair in combinations(range(4), 2):
                for support in components(adj, state, pair):
                    if support <= S:
                        next_state, _ = switch(adj, state, pair, min(support))
                        physical[cs].add(tuple(next_state[x] for x in cycle))
        classes = connected_components(physical)
        require(len(classes) == len(record['classes']), 'Class count mismatch')
        index = cycle.index(anchor)
        observed = sorted(sorted({cs[index] for cs in group}) for group in classes)
        require(observed == sorted(record['classes']), 'Class partition mismatch')
        record.update(full_assignments=len(states), physical_classes=len(classes), brute_crosscheck=True)
    return record


def verify(here):
    path = here / 'cycle-anchors-example.json'
    fixture = json.loads(path.read_text())
    source = here / fixture['source']
    require(sha256(source.read_bytes()).hexdigest() == fixture['source_sha256'], 'Source pin differs')
    case = json.loads(source.read_text())['cases'][fixture['source_case']]
    verify_case(here, case)
    adj, current = whole_case(here, case)
    records = []
    for selected in fixture['cases']:
        cycle, anchor = selected['cycle'], selected['anchor']
        S = set(cycle)
        require(3 <= len(cycle) <= 7 and len(S) == len(cycle), 'Invalid bounded cycle')
        require(S <= adj.keys() and anchor in S, 'Foreign vertex or missing anchor')
        require(all(adj[x] & S == {cycle[(i-1) % len(cycle)], cycle[(i+1) % len(cycle)]}
                    for i, x in enumerate(cycle)), 'Not the claimed induced cycle')
        if 'centre' in selected:
            require(adj[selected['centre']] == S, 'Cycle does not surround the claimed centre')
        record = analyse(adj, current, cycle, anchor, check=True)
        require(record['feasible'] == selected['feasible_colours'], 'Feasible anchor colours differ')
        require([r['pair'] for r in record['transitions']] == selected['transitions'],
                'Exact anchor transitions differ')
        require(record['classes'] == selected['classes'], 'Anchor classes differ')
        record.update(name=selected['name'], ambient_vertices=len(adj),
                      exterior_vertices=len(adj) - len(S), hidden_forest_vertices=len(S) - 1,
                      source_degree_range=[min(map(len, adj.values())), max(map(len, adj.values()))],
                      source_repair_replayed=True, concrete_instance_kernel_certified=False)
        records.append(record)
    return {'evidence': 'Independent program checks of the generic cycle-anchor contract.',
            'cases': records,
            'kernel_theorems': ['SimpleGraph.KempeCycleAnchors.same_anchor_path',
                               'SimpleGraph.KempeCycleAnchors.one_anchor_card_le_four',
                               'SimpleGraph.KempeCycleAnchors.history_iff'],
            'scope': 'Anchor colours distinguish fixed-exterior physical classes when their deletion '
                    'leaves a forest. Exact guard transitions reconstruct actual histories. Neither '
                    'all anchor colours nor all transitions need be feasible. No bounded anchor set '
                    'for arbitrary maps, ordinary smaller-map reduction, global coverage or net '
                    'proof-cost saving is asserted.',
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
