#!/usr/bin/env python3
"""Replay fixed-region obstructions and the successful larger-region repairs.

The finite census is program evidence. The arbitrary-colouring obstruction
and two singleton instances have separate Lean proofs. No repair search or
long-history enumeration is used here.
"""
import argparse
from collections import deque
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_component_detach import PAIRS, data, lean_literals
from audit_diamond_sources import require
from probe_flat_pairs import geometry


def odd_cycle(adj, vertices):
    """Return and independently check an odd cycle, or a two-colouring."""
    colour, parent = {}, {}
    for root in sorted(vertices):
        if root in colour:
            continue
        colour[root], parent[root] = 0, None
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in sorted(adj[u] & vertices):
                if v not in colour:
                    colour[v], parent[v] = 1-colour[u], u
                    queue.append(v)
                elif colour[u] == colour[v]:
                    paths = []
                    for start in (u, v):
                        path = []
                        while start is not None:
                            path.append(start)
                            start = parent[start]
                        paths.append(path)
                    left, right = paths
                    meet = next(x for x in left if x in right)
                    cycle = left[:left.index(meet)+1] + right[:right.index(meet)][::-1] + [u]
                    check_cycle(adj, vertices, cycle)
                    return cycle
    require(set(colour) == vertices and all(colour[u] != colour[v]
            for u in vertices for v in adj[u] & vertices), 'Invalid bipartition')
    return None


def check_cycle(adj, vertices, cycle):
    require(cycle[0] == cycle[-1] and (len(cycle)-1) % 2 == 1, 'Cycle not closed and odd')
    require(len(set(cycle[:-1])) == len(cycle)-1, 'Cycle repeats a vertex')
    require(set(cycle) <= vertices and all(v in adj[u] for u, v in zip(cycle, cycle[1:])),
            'Invalid cycle edge or support')


def regions(adj, colours, ports):
    """Each one-exit connected region is one shore of a bichromatic bridge."""
    for pair in PAIRS:
        for block in components(adj, colours, pair):
            for u in sorted(block):
                for v in sorted(adj[u] & block):
                    if u >= v:
                        continue
                    shore, todo = {u}, [u]
                    while todo:
                        x = todo.pop()
                        for y in adj[x] & block:
                            if {x, y} != {u, v} and y not in shore:
                                shore.add(y)
                                todo.append(y)
                    if v in shore:
                        continue
                    for region, x, y in ((shore, u, v), (block-shore, v, u)):
                        if region & ports:
                            continue
                        exits = [(s, z) for s in sorted(region) for z in sorted(adj[s]-region)
                                 if colours[z] in pair]
                        require(exits == [(x, y)], 'Region has more than the stated exit')
                        yield pair, region, x, y


def verify(here):
    fixture, ambient, adj, ports, colours, _, _, traces, _, census, repairs = data(here)
    darts, *_ = geometry(fixture['faces'])
    boundary, records = set(ports), []
    for pair, region, x, y in regions(adj, colours, boundary):
        a, c = colours[y], colours[x]
        choices = []
        for b in sorted(set(range(4))-{a, c}):
            target, component = switch(adj, colours, (a, b), y)
            proper(adj, target)
            entries = [(s, z) for s in sorted(region) for z in sorted(adj[s] & component)
                       if colours[z] == b]
            success = not (component & boundary) and not entries
            if success:
                require(not component & region, 'Successful switch changes the retained region')
                actual = next(k for k in components(adj, target, pair) if x in k)
                require(actual == region, 'The claimed detachment did not occur')
            choices.append({'transverse_colour': b, 'component': sorted(component),
                            'boundary_hits': sorted(component & boundary), 'entries': entries,
                            'detaches': success})
        outside = set().union(*(adj[s] for s in region))-region
        cycle = odd_cycle(adj, outside)
        success = any(t['detaches'] for t in choices)
        require(not (cycle and success), 'Detachment contradicts the odd boundary witness')
        wings = [darts[x, y][1], darts[y, x][1]]
        records.append({'pair': list(pair), 'region': sorted(region), 'exit': [x, y],
                        'facial_corners': wings, 'corner_colours': [colours[w] for w in wings],
                        'choices': choices, 'odd_external_cycle': cycle, 'detaches': success})
    counts = {'oriented_one_exit_regions': len(records),
              'one_switch_detachments': sum(r['detaches'] for r in records),
              'odd_external_boundary_obstructions': sum(r['odd_external_cycle'] is not None for r in records),
              'bipartite_boundary_one_switch_failures': sum(not r['detaches'] and r['odd_external_cycle'] is None for r in records)}
    require(counts == {'oriented_one_exit_regions': 332, 'one_switch_detachments': 24,
                      'odd_external_boundary_obstructions': 233,
                      'bipartite_boundary_one_switch_failures': 75}, 'Census changed')
    specimen = next(r for r in records if r['region'] == [62] and r['exit'] == [62, 70])
    require(all(not c['boundary_hits'] and c['entries'] for c in specimen['choices']),
            'The local supply counterexample changed')
    carrier = sorted(adj)
    labels = {v: i for i, v in enumerate(carrier)}
    consumers = []
    for seed, cycle in ((79, [16,77,81,64,116,16]), (112, [94,155,159,150,152,94])):
        check_cycle(adj, adj[seed], cycle)
        support = []
        for trace in traces:
            region = set(trace[1])
            require({seed} < region, 'Repair does not enlarge the obstructed singleton')
            require(odd_cycle(adj, set().union(*(adj[s] for s in region))-region) is None,
                    'A detached region still has an odd external boundary')
            support.append(len(region))
        consumers.append({'sphere_seed': seed, 'exterior_seed': labels[seed],
                          'neighbour_cycle_sphere': cycle,
                          'neighbour_cycle_exterior': [labels[v] for v in cycle],
                          'successful_larger_region_sizes': support})
    root = here.parents[2]
    source = (root / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/ComponentDetachExample.lean').read_text()
    for key, literal in lean_literals(here).items():
        definitions = [line for line in source.splitlines() if line.startswith(f'def {key} :')]
        require(len(definitions) == 1 and definitions[0].split(' := ', 1)[-1] == literal,
                f'Lean graph or history differs for {key}')
    parity_path = root / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/BoundaryParityAudit.lean'
    parity = parity_path.read_text()
    require('if j = 0 then 74 else 105' in parity, 'Lean seed labels differ')
    for consumer in consumers:
        literal = '[' + ','.join(map(str, consumer['neighbour_cycle_exterior'])) + ']'
        require(literal in parity, 'Lean neighbour walk differs')
    return {'evidence': 'Finite geometry and census are program checked. The arbitrary-colouring obstruction and two consumed singleton instances are Lean checked.',
            'fixture_sha256': sha256((here / 'component-detach-example.json').read_bytes()).hexdigest(),
            'lean_consumer_sha256': sha256(parity_path.read_bytes()).hexdigest(),
            'geometry': census, 'counts': counts,
            'census_sha256': sha256(json.dumps(records, sort_keys=True).encode()).hexdigest(),
            'supply_counterexample': specimen, 'lean_consumers': consumers,
            'reconstructed_colouring_count': len(repairs),
            'scope': 'An odd external boundary forbids a fixed region from being a two-colour component in every proper four-colouring. '
                     'It does not forbid a larger region or other decompositions. Bipartite external boundary alone supplies neither detachment nor progress. '
                     'No new coverage or complete-proof certificate removal is claimed.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
