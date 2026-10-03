#!/usr/bin/env python3
"""Replay a component detachment, composed repairs and a bounded obstruction.

The exact spherical geometry and one-silent-switch failure are program
evidence. The general detachment law and the two specified physical repair
histories are checked separately in Lean. No recolouring search is needed
to replay the supplied successful histories.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_clique_fill import make_profile
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_odd_mesh import cycle_census
from audit_two_port_core import eliminate
from probe_flat_pairs import geometry

PAIRS = tuple(combinations(range(4), 2))


def chain(adj, support, root):
    """A spanning tree tour certifies connectivity without enumerating walks."""
    seen, result = {root}, [root]
    def visit(v):
        for u in sorted(adj[v] & support):
            if u not in seen:
                seen.add(u)
                result.append(u)
                visit(u)
                result.append(v)
    visit(root)
    require(seen == support, 'Disconnected purported component')
    return result


def phase_census(adj, colours, ports, profile, threshold):
    """All boundary endpoints of an arbitrarily long fixed-pair phase."""
    result = []
    for pair in PAIRS:
        blocks = [s for s in components(adj, colours, pair) if s.intersection(ports)]
        counts = Counter()
        for mask in range(2 ** len(blocks)):
            target = dict(colours)
            for i, support in enumerate(blocks):
                if mask >> i & 1:
                    target, actual = switch(adj, target, pair, min(support))
                    require(actual == support, 'Fixed-pair support changed')
            score = profile([target[v] for v in ports])
            counts['improving' if score > threshold else 'equal' if score == threshold else 'worse'] += 1
        result.append({'pair': list(pair), 'boundary_components': len(blocks), **counts})
    return result


def data(here):
    path = here / 'component-detach-example.json'
    fixture = json.loads(path.read_text())
    for name, expected in ((fixture['source_fixture'], fixture['source_fixture_sha256']),
                           (fixture['configuration'], fixture['configuration_sha256'])):
        require(sha256((here / name).read_bytes()).hexdigest() == expected, 'Source pin differs')
    raw = (here / fixture['configuration']).read_bytes()
    ring, patch = graph(raw)
    images, ports = fixture['images'], fixture['images'][:ring]
    removed = set(images[ring:])
    require(len(images) == len(patch) and len(set(images)) == len(images), 'Invalid occurrence carrier')
    _, ambient, nexts, prevs = geometry(fixture['faces'])
    census = cycle_census(fixture['faces'])
    require(census['minimum_degree'] >= 5 and census['obstructing_cycles'] == 0,
            'The sphere has an obstructing short cycle')
    rows = [list(map(int, row.split())) for row in raw.decode().splitlines() if row.strip()]
    require(fixture['orientation'] in ('forward', 'reverse'), 'Unknown source orientation')
    rotation = nexts if fixture['orientation'] == 'forward' else prevs
    for v, degree, *neighbours in rows[1:]:
        actual = images[v-1]
        require(ambient[actual] == {images[u-1] for u in neighbours}, 'Complete core star differs')
        require(len(ambient[actual]) == degree, 'Prescribed core degree differs')
        require(all(rotation[actual, images[a-1]] == images[b-1]
                    for a, b in zip(neighbours, neighbours[1:] + neighbours[:1])),
                'Cyclic core order differs')
    require(all(images[v] in ambient[images[u]] for u in range(len(patch)) for v in patch[u]),
            'An ordered source edge is missing')
    exterior = {v: ns-removed for v, ns in ambient.items() if v not in removed}
    require(len(fixture['colouring']) == len(ambient), 'Wrong colouring carrier')
    require({v for v, c in enumerate(fixture['colouring']) if c is None} == removed,
            'The missing colours do not match the source core')
    initial = {v: c for v, c in enumerate(fixture['colouring']) if c is not None}
    proper(exterior, initial)
    profile = make_profile(patch, ring)
    value = profile([initial[v] for v in ports])
    require(value[0] == 0, 'The initial boundary already extends')
    states, traces, complete, repair_reports = [initial], [], [], []
    for repair in fixture['repairs']:
        current, histories, commands = dict(initial), [], repair['prepare'] + [repair['finish']]
        supports = []
        for j, command in enumerate(commands):
            target, support = switch(exterior, current, command['pair'], command['root'])
            if j < 2:
                require(not support.intersection(ports) and len(support) == command['size'],
                        'The specified preparation is not boundary-silent')
            histories.append(chain(exterior, support, command['root']))
            supports.append(support)
            states.append(target)
            current = target
        first, detached = supports[:2]
        a, b = commands[0]['pair']
        require(commands[1]['pair'][0] == a, 'Expected a shared colour')
        c = commands[1]['pair'][1]
        require(len({a, b, c}) == 3 and not first & detached, 'Invalid detachment colours or overlap')
        old_exits = [(x, y) for x in sorted(detached) for y in sorted(exterior[x]-detached)
                     if initial[y] in (a, c)]
        require(old_exits and all(y in first for _, y in old_exits), 'An old active exit remains')
        require(all(initial[y] != b for x in detached for y in exterior[x] & first),
                'A new active neighbour enters the detached set')
        old_component = next(s for s in components(exterior, initial, (a, c))
                             if commands[1]['root'] in s)
        require(old_component.intersection(ports), 'The selected component was already silent')
        boundary = [current[v] for v in ports]
        core, _ = eliminate(patch, ring, boundary)
        require(core is not None, 'The repaired boundary does not extend')
        completed = current | {images[v]: colour for v, colour in core.items()}
        proper(ambient, completed)
        complete.append(completed)
        traces.append(histories)
        repair_reports.append({'commands': commands, 'component_sizes': list(map(len, supports)),
            'old_active_exit_edges': old_exits, 'old_component_boundary': sorted(old_component.intersection(ports)),
            'detached_component_boundary': [], 'final_boundary': boundary,
            'initial_profile': value, 'prepared_profiles': [value, value],
            'final_profile': profile(boundary), 'whole_colouring_reconstructed': True})
    return fixture, ambient, exterior, ports, initial, profile, states, traces, complete, census, repair_reports


def lean_literals(here):
    fixture, ambient, exterior, ports, initial, profile, states, traces, complete, census, reports = data(here)
    carrier = sorted(exterior)
    labels = {v: i for i, v in enumerate(carrier)}
    pair_text = lambda es: '[' + ','.join(f'({u},{v})' for u, v in es) + ']'
    list_text = lambda xs: '[' + ','.join(map(str, xs)) + ']'
    edges = sorted((labels[u], labels[v]) for u in exterior for v in exterior[u] if u < v)
    ambient_edges = sorted((u, v) for u in ambient for v in ambient[u] if u < v)
    literals = {
        'edges': pair_text(edges), 'ambientEdges': pair_text(ambient_edges),
        'carrier': list_text(carrier), 'ports': list_text(labels[v] for v in ports),
        'colourData': list_text(sum(state[v] << (2*j) for j,v in enumerate(carrier)) for state in states),
        'completeData': list_text(sum(state[v] << (2*j) for j,v in enumerate(sorted(ambient))) for state in complete)}
    for i, history in enumerate(traces):
        for j, trace in enumerate(history):
            literals[f'trace{i}{j}'] = list_text(labels[v] for v in trace)
    return literals


def verify(here, check_lean=True):
    fixture, ambient, exterior, ports, initial, profile, states, traces, complete, census, repairs = data(here)
    threshold = profile([initial[v] for v in ports])
    initial_phases = phase_census(exterior, initial, ports, profile, threshold)
    require(all(p.get('improving', 0) == 0 for p in initial_phases), 'An initial phase improves')
    preparations = []
    for pair in PAIRS:
        for support in components(exterior, initial, pair):
            if support.intersection(ports):
                continue
            prepared, actual = switch(exterior, initial, pair, min(support))
            require(actual == support, 'Preparation support changed')
            report = phase_census(exterior, prepared, ports, profile, threshold)
            require(all(p.get('improving', 0) == 0 for p in report),
                    'One silent component already exposes an improving phase')
            preparations.append({'pair': list(pair), 'root': min(support), 'size': len(support),
                                 'following_phases': report})
    require(len(preparations) == 17, 'The exhaustive silent preparation count changed')
    # A single phase may switch several disjoint components. Its success
    # must not be confused with the failed single-component bound above.
    command = fixture['simultaneous_silent_phase']
    require(len(command['roots']) == len(command['sizes']) == 2,
            'Expected two independent components in the silent phase')
    initial_components = components(exterior, initial, command['pair'])
    prepared, supports = dict(initial), []
    for root, size in zip(command['roots'], command['sizes']):
        prepared, support = switch(exterior, prepared, command['pair'], root)
        require(len(support) == size and not support.intersection(ports),
                'The simultaneous preparation touches the boundary')
        require(all(not support & old for old in supports), 'Preparatory components overlap')
        require(support in initial_components, 'A component was not present at the phase start')
        supports.append(support)
    final, _ = switch(exterior, prepared, command['finish']['pair'], command['finish']['root'])
    ring, patch = graph((here / fixture['configuration']).read_bytes())
    core, _ = eliminate(patch, ring, [final[v] for v in ports])
    require(core is not None, 'The simultaneous silent phase does not enable repair')
    proper(ambient, final | {fixture['images'][v]: c for v, c in core.items()})
    phase_repair = {'commands': command, 'whole_colouring_reconstructed': True,
                   'evidence': 'Program checked; distinct from the two Lean detachment histories.'}
    lean_sha = None
    if check_lean:
        path = here.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/ComponentDetachExample.lean'
        source = path.read_text()
        for key, literal in lean_literals(here).items():
            definitions = [line for line in source.splitlines() if line.startswith(f'def {key} :')]
            require(len(definitions) == 1 and definitions[0].split(' := ', 1)[-1] == literal,
                    f'Lean data differ for {key}')
        lean_sha = sha256(path.read_bytes()).hexdigest()
    return {'evidence': 'Spherical geometry and exhaustive bounded failure are program checked; the detachment law and two successful histories have separate Lean proofs.',
        'fixture_sha256': sha256((here / 'component-detach-example.json').read_bytes()).hexdigest(),
        'lean_example_sha256': lean_sha, 'geometry': census, 'initial_phase_census': initial_phases,
        'all_boundary_silent_preparations': preparations, 'repairs': repairs,
        'one_simultaneous_silent_phase_also_succeeds': phase_repair,
        'scope': 'Refutes at most one silent component followed by one fixed-pair phase as a universally improving count-potential strategy on this source domain. '
                 'Two specified silent preparations and one further switch reconstruct the whole colouring. '
                 'A single simultaneous silent phase also succeeds here. Does not rule out other potentials, temporary decrease, longer preparations or compact compositional Four Colour proofs. No coverage reduction.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--skip-lean-match', action='store_true')
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent, not args.skip_lean_match)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
