#!/usr/bin/env python3
"""Replay a repair obtained by composing the same detachment law twice.

The sphere and original colouring are reused exactly. A bounded census
distinguishes useful preparations from merely detachable regions. Lean
separately checks the selected physical history and whole reconstruction.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_boundary_parity import regions, odd_cycle
from audit_component_detach import PAIRS, data, chain, lean_literals
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_two_port_core import eliminate


def phase_words(adj, colours, ports, profile, threshold):
    good = []
    for pair in PAIRS:
        blocks = [s for s in components(adj, colours, pair) if s.intersection(ports)]
        for mask in range(1 << len(blocks)):
            word = [pair[1] if colours[v] == pair[0] else pair[0]
                    if colours[v] == pair[1] else colours[v] for v in ports]
            word = [word[j] if any(mask >> i & 1 and v in s for i, s in enumerate(blocks))
                    else colours[v] for j, v in enumerate(ports)]
            value = profile(word)
            if value > threshold:
                good.append({'pair': list(pair), 'mask': mask, 'extends': value[0] > 0,
                             'boundary': word})
    return good


def verify(here):
    request = json.loads((here / 'cascading-detach-example.json').read_text())
    require(sha256((here / request['base_fixture']).read_bytes()).hexdigest() ==
            request['base_fixture_sha256'], 'Base fixture changed')
    f, ambient, adj, ports, initial, profile, *_ = data(here)
    B, threshold = set(ports), profile([initial[v] for v in ports])
    states, supports, traces, current = [], [], [], dict(initial)
    for i, cmd in enumerate(request['commands']):
        current, support = switch(adj, current, cmd['pair'], cmd['root'])
        require(len(support) == cmd['size'], 'Component size differs')
        proper(adj, current)
        if i < 2:
            require(not support & B, 'A preparation changes a protected port')
        supports.append(support)
        traces.append(chain(adj, support, cmd['root']))
        states.append(current)
    detachment = []
    for i in range(2):
        old = initial if i == 0 else states[i-1]
        first, target = supports[i:i+2]
        a, b = request['commands'][i]['pair']
        pair = request['commands'][i+1]['pair']
        require(a in pair and b not in pair and not first & target, 'Invalid linked pairs or support')
        exits = [(x, y) for x in sorted(target) for y in sorted(adj[x]-target) if old[y] in pair]
        require(exits and all(y in first for _, y in exits), 'An old exit is not switched away')
        require(all(old[y] != b for x in target for y in adj[x] & first), 'A new active entry appears')
        detachment.append({'old_active_exits': exits, 'preceding_component_size': len(first),
                           'new_component_size': len(target)})
    touched = supports[0] | supports[1]
    require(len(touched) == 5, 'Preparation support changed')
    ring, patch = graph((here / f['configuration']).read_bytes())
    boundary = [current[v] for v in ports]
    core, _ = eliminate(patch, ring, boundary)
    require(core is not None, 'The selected boundary does not extend')
    complete = current | {f['images'][v]: c for v, c in core.items()}
    proper(ambient, complete)

    # Enumerate precisely the old one-exit regions and their two transverse
    # components, then check every boundary outcome of one final fixed pair.
    candidates = []
    for pair, S, x, y in regions(adj, initial, B):
        for b in sorted(set(range(4))-set(pair)):
            first, K = switch(adj, initial, (initial[y], b), y)
            entries = [(u, v) for u in S for v in adj[u] & K if initial[v] == b]
            if K & B or entries:
                continue
            prepared, actual = switch(adj, first, pair, min(S))
            require(actual == S and not K & S, 'Candidate does not detach exactly')
            good = phase_words(adj, prepared, ports, profile, threshold)
            candidates.append({'pair': list(pair), 'region_size': len(S), 'exit': [x, y],
                               'first_size': len(K), 'improving_outcomes': len(good),
                               'extending_outcomes': sum(g['extends'] for g in good)})
    require(len(candidates) == 24 and sum(r['extending_outcomes'] > 0 for r in candidates) == 6,
            'Useful-detachment census changed')
    # Proper enlargement need not preserve even this necessary condition.
    nested = []
    for size in (9, 11):
        S = next(S for pair, S, _, _ in regions(adj, initial, B)
                 if pair == (0, 1) and 8 in S and len(S) == size)
        outside = set().union(*(adj[v] for v in S))-S
        nested.append({'region': sorted(S), 'odd_external_cycle': odd_cycle(adj, outside)})
    require(set(nested[0]['region']) < set(nested[1]['region']) and
            nested[0]['odd_external_cycle'] is None and nested[1]['odd_external_cycle'],
            'Nested-region obstruction changed')

    carrier = sorted(adj)
    labels = {v: i for i, v in enumerate(carrier)}
    pack = lambda state: sum(state[v] << (2*i) for i, v in enumerate(sorted(state)))
    literal = lambda xs: '[' + ','.join(map(str, xs)) + ']'
    definitions = {'colourData': literal(map(pack, states)), 'completeData': str(pack(complete))}
    definitions.update({f'trace{i}': literal(labels[v] for v in trace) for i, trace in enumerate(traces)})
    root = here.parents[2]
    lean = root / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/CascadingDetach.lean'
    source = lean.read_text()
    for key, value in definitions.items():
        lines = [line for line in source.splitlines() if line.startswith(f'def {key} :')]
        require(len(lines) == 1 and lines[0].split(' := ', 1)[-1] == value, f'Lean {key} differs')
    base = (root / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/ComponentDetachExample.lean').read_text()
    for key, value in lean_literals(here).items():
        lines = [line for line in base.splitlines() if line.startswith(f'def {key} :')]
        require(len(lines) == 1 and lines[0].split(' := ', 1)[-1] == value, f'Base Lean {key} differs')
    return {'evidence': 'Selected physical history, five-vertex preparation support and whole reconstruction are Lean checked. The exhaustive restricted census and nested-region geometry are program evidence.',
            'fixture_sha256': sha256((here / 'cascading-detach-example.json').read_bytes()).hexdigest(),
            'lean_sha256': sha256(lean.read_bytes()).hexdigest(), 'commands': request['commands'],
            'detachment_links': detachment, 'preparation_vertices': sorted(touched),
            'final_boundary': boundary, 'initial_profile': threshold, 'final_profile': profile(boundary),
            'whole_graph_vertices': len(ambient), 'whole_colouring_reconstructed': True,
            'detachable_candidates': len(candidates),
            'candidates_enabling_extension_after_one_phase': 6, 'candidate_census': candidates,
            'enlargement_can_create_an_odd_boundary': nested,
            'scope': 'The same general law is consumed twice, on the same exterior. This is one additional checked repair, not a universal source repair theorem. '
                     'Five preparation vertices improves the displayed histories; no global optimality claim. '
                     'The census is restricted to one-exit regions and the stated three-stage shape. No coverage or catalogue dependency is removed.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
