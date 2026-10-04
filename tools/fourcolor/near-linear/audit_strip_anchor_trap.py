#!/usr/bin/env python3
"""Independently replay the physical joint-anchor trap and its escape.

The solver enumerates omitted-vertex sets and searches compatible partial
colourings directly. Lean uses triangle elimination instead. No full repair
table is emitted. The universal-history theorem is in StripAnchorTrapHistory.
"""
import argparse
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations, product
import json
from pathlib import Path
import re

from audit_boundary_observation import proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_phase import geometry


def normalize(colours):
    names = {}
    return tuple(names.setdefault(a, len(names)) for a in colours)


def direct_solver(source, ring, anchors):
    """Exact minimum omissions for each joint anchor assignment."""
    rest = sorted(set(range(len(source) - ring)) - set(anchors))

    @lru_cache(None)
    def witness(boundary, holes, choice):
        active = set(range(len(source) - ring)) - set(holes)
        colours = dict(zip(anchors, choice))
        if any(boundary[j] == a for v, a in colours.items()
               for j in source[ring + v] if j < ring):
            return None

        def visit(left):
            if not left:
                return dict(colours)
            allowed = {v: set(range(4)) -
                       {boundary[j] for j in source[ring + v] if j < ring} -
                       {a for u, a in colours.items() if ring + u in source[ring + v]}
                       for v in left}
            v = min(left, key=lambda u: (len(allowed[u]), u))
            for a in sorted(allowed[v]):
                colours[v] = a
                result = visit(left - {v})
                if result is not None:
                    return result
            colours.pop(v, None)
            return None

        return visit(active - set(anchors))

    @lru_cache(None)
    def profile(boundary):
        costs = []
        for choice in product(range(4), repeat=2):
            best = next((k for k in range(len(rest) + 1)
                         if any(witness(boundary, hs, choice) is not None
                                for hs in combinations(rest, k))), 99)
            costs.append(best)
        minimum = min(costs)
        return (minimum, -costs.count(minimum)), costs

    return profile, witness


def batches(adj, colours):
    """Independent flood fill and all subsets of complete components."""
    for pair in combinations(range(4), 2):
        unseen = {v for v, a in enumerate(colours) if a in pair}
        blocks = []
        while unseen:
            todo = [min(unseen)]
            block = set(todo)
            unseen -= block
            for v in todo:
                for u in adj[v]:
                    if u in unseen:
                        unseen.remove(u)
                        block.add(u)
                        todo.append(u)
            blocks.append(sorted(block))
        for mask in range(1 << len(blocks)):
            support = {v for i, block in enumerate(blocks) if mask >> i & 1 for v in block}
            out = tuple((pair[1] if colours[v] == pair[0] else pair[0])
                        if v in support else colours[v] for v in range(len(colours)))
            proper(adj, dict(enumerate(out)))
            yield out, pair, blocks, mask


def definition(text, name):
    match = re.search(rf'^def {name}\b(.*?)(?=^(?:def |theorem |instance |private |/--|'
                      r'noncomputable |end ))', text, re.M | re.S)
    require(match is not None, f'Missing Lean definition: {name}')
    return re.sub(r'\s+', '', match[1]).split(':=', 1)[-1]


def verify(here):
    fixture = here / 'strip-anchor-trap-example.json'
    f = json.loads(fixture.read_text())
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() == f['source_sha256'], 'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19 and f['anchors'] == [1, 6], 'Source carriers')
    initial = tuple(f['colouring'])
    adj = geometry(f['faces'], list(range(ring)))
    require(len(adj) == len(initial) == 12, 'Exterior carrier')
    proper(adj, dict(enumerate(initial)))
    profile, witness = direct_solver(source, ring, tuple(f['anchors']))
    initial_score, initial_costs = profile(initial[:ring])
    require(initial_score == (1, -4) and initial_costs == f['initial_costs'], 'Initial choices')
    scores = Counter()
    palette_only = 0
    component_counts = []
    for out, pair, blocks, mask in batches(adj, initial):
        score, _ = profile(out[:ring])
        same = normalize(out) == normalize(initial)
        require(score > initial_score or same, 'Nonworsening escape found')
        scores[score] += 1
        palette_only += same
        if mask == 0:
            component_counts.append({'pair': pair, 'components': len(blocks), 'subsets': 1 << len(blocks)})
    require(sum(scores.values()) == 38 and palette_only == 12, 'Batch counts')
    for perm in permutations(range(4)):
        renamed = tuple(perm[a] for a in initial)
        require(profile(renamed[:ring])[0] == initial_score, 'Palette covariance')
        for out, _, _, _ in batches(adj, renamed):
            require(profile(out[:ring])[0] > initial_score or
                    normalize(out) == normalize(initial), 'Renamed escape found')

    states = [dict(enumerate(initial))]
    history = []
    for cmd in f['commands']:
        new, support = switch(adj, states[-1], cmd['pair'], cmd['root'])
        history.append({'pair': cmd['pair'], 'support': sorted(support),
                        'before': profile(tuple(states[-1][i] for i in range(ring)))[0],
                        'after': profile(tuple(new[i] for i in range(ring)))[0]})
        states.append(new)
    require([h['after'] for h in history] == [(1, -1), (0, -1)], 'Escape profiles')
    b = tuple(states[-1][i] for i in range(ring))
    require(witness(b, (), (2, 0)) is not None, 'No final source colouring')
    completed = dict(enumerate(b)) | {ring + v: a for v, a in enumerate(f['final_core'])}
    proper(dict(enumerate(source)), completed)
    source_vertex = lambda v: v if v < ring else v + 1
    triangles = [list(t) for t in combinations(range(19), 3)
                 if all(v in source[u] for u, v in combinations(t, 2))]
    whole_faces = f['faces'] + [[source_vertex(v) for v in t] for t in triangles]
    whole = geometry(whole_faces, [])
    require(len(whole) == 20, 'Glued carrier')
    final = states[-1] | {12 + v: a for v, a in enumerate(f['final_core'])}
    proper(whole, final)
    for v in range(11, 19):
        require(whole[source_vertex(v)] == {source_vertex(w) for w in source[v]}, 'Core star')

    lean_dir = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    text = (lean_dir / 'StripAnchorTrap.lean').read_text()
    star = json.loads(definition(text, 'star').removeprefix('!'))
    require(len(star) == 12 and all(set(star[v]) == adj[v] for v in adj), 'Lean exterior differs')
    values = definition(text, 'values')
    for i, state in enumerate(states):
        row = '![' + ','.join('c' + str(state[v]) for v in range(12)) + ']'
        require(f'|{i}=>{row}' in values, 'Lean colouring differs')
    repair = (lean_dir / 'StripAnchorTrapHistory.lean').read_text()
    require(definition(repair, 'finalCore') == '![' +
            ','.join('c' + str(a) for a in f['final_core']) + ']', 'Lean core differs')
    return {
        'classification': 'PHYSICAL_NONWORSENING_ANCHOR_TRAP_WITH_TWO_SWITCH_ESCAPE',
        'source': 'D0099', 'source_sha256': f['source_sha256'],
        'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
        'attribution': 'Yuta Inoue D0099 catalogue, MIT; source semantics from Gonthier/Emery.',
        'exterior_vertices': 12, 'whole_vertices': 20, 'anchors': f['anchors'],
        'initial_score': initial_score, 'initial_costs': initial_costs,
        'component_batches': component_counts,
        'batch_score_counts': [{'score': s, 'count': n} for s, n in sorted(scores.items())],
        'palette_only_batches': palette_only, 'palette_permutations_checked': 24,
        'escape': history, 'exterior_degrees': sorted(len(x) for x in adj.values()),
        'whole_degrees': sorted(len(x) for x in whole.values()),
        'evidence': 'Lean proves exterior planarity, all-phase obstruction, arbitrary-history '
                    'invariance, exact anchored reconstruction and the physical two-switch escape. '
                    'Exact numerical minimum-hole costs and whole-sphere geometry are independent program checks.',
        'limits': ['This is one actual exterior of D0099, with low-degree vertices.',
                   'Minimal-counterexample hypotheses are not established.',
                   'The obstruction concerns the specified nonworsening rank, not unrestricted repair.',
                   'No universal coverage, strict reduction or catalogue deletion is established.'],
        'fixture_sha256': sha256(fixture.read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
