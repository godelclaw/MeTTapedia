#!/usr/bin/env python3
"""Independently replay the small two-stage punctured-source strategy.

The verifier enumerates noncrossing matchings to check the Lean interval
selection independently, then reconstructs a partial source colouring for
every terminal contract. It stores no matching or colouring witness table.
The symbolic elimination and same-exterior reconstruction are Lean theorems.
"""
import argparse
import ast
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_partial import partial
from generate_exceptional_repair import boundary, canonical, pairings


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source carrier differs')
    path = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripTwoPhaseProgress.lean'
    text = path.read_text()

    def definition(name):
        m = re.search(rf'^def {name}\b(.*?)(?=^(?:def |theorem |instance |/--|end ))',
                      text, re.M | re.S)
        require(m is not None, f'Missing definition {name}')
        return m[1]

    def rows(name):
        values = re.findall(r'^\s*\| (\d+) => (.*)$', definition(name), re.M)
        require([int(i) for i, _ in values] == list(range(9)), 'Wrong stage rows')
        return [ast.literal_eval(re.sub(r'c([0-3])', r'\1', s).replace('!', ''))
                for _, s in values]

    words = rows('source')
    singles, doubles = rows('singles'), rows('doubles')
    palettes = re.findall(r'\.e([123]{3})', definition('palette'))
    anchors = [ast.literal_eval(definition(name).split(':= !', 1)[1])
               for name in ('anchor0', 'anchor1')]
    require(len(palettes) == 9, 'Wrong palette count')
    require([''.join(map(str, w)) for w in words[5:]] ==
            ['12311221133', '12311331133', '12312332133', '12313223133'],
            'Initial domain differs')
    middle = {canonical(w): i for i, w in enumerate(words[:5])}
    require(len(middle) == 5, 'Intermediate words repeat')

    def witnesses(w):
        require(len(w) == ring and all(c in (1, 2, 3) for c in w), 'Improper edge trace')
        b = boundary(w)
        require(all(b[u] != b[v] for u in range(ring) for v in source[u] if v < ring),
                'A boundary source edge conflicts')
        result = []
        for h in range(8):
            f = partial(source, ring, b, [h])
            if f is None:
                continue
            colours = dict(enumerate(b)) | f
            require(set(colours) == set(range(19)) - {ring + h}, 'Missing retained vertex')
            require(all(colours[u] != colours[v] for u in colours for v in source[u] if v in colours),
                    'Invalid partial source witness')
            result.append(h)
        return result

    initial = []
    for w in words[5:]:
        require(not witnesses(w), 'An initial input already has a one-hole witness')
        b = boundary(w)
        two = next(((u, v) for u in range(8) for v in range(u+1, 8)
                    if partial(source, ring, b, [u, v]) is not None), None)
        require(two is not None, 'An initial input needs more than two holes')
        initial.append({'word': ''.join(map(str, w)), 'minimum_holes': 2})

    stages = []
    for s, w in enumerate(words):
        perm = [0] + list(map(int, palettes[s]))
        c = tuple(perm[x] for x in w)
        a, b = (xs[s] for xs in anchors)
        require(c[a] != 1 and c[b] != 1, 'Inactive anchor')
        contracts = []
        for kind, commands in [('single', singles[s]), ('double', doubles[s])]:
            for p, q in commands:
                selected = [(p, q)] if kind == 'single' else [(a, p), (b, q)]
                out = flip(c, 1, selected)
                continuation = middle.get(canonical(out)) if s >= 5 else None
                holes = [] if continuation is not None else witnesses(out)
                require(continuation is not None or holes, 'Unproved terminal contract')
                contracts.append({'kind': kind, 'partners': [p, q],
                                  'middle': continuation, 'allowed_holes': holes})
        active = [i for i, x in enumerate(c) if x != 1]
        layout_count = 0
        pair_count = 0
        single_set = {tuple(sorted(p)) for p in singles[s]}
        for m in pairings(len(active)):
            pairs = [(active[i], active[j]) for i, j in m]
            mate = {x: y for i, j in pairs for x, y in [(i, j), (j, i)]}
            layout_count += 1
            if any(tuple(sorted(p)) in single_set for p in pairs):
                continue
            require((mate[a], mate[b]) in doubles[s], 'Uncovered matching')
            pair_count += 1
        stages.append({'word': ''.join(map(str, w)), 'palette': palettes[s],
                       'anchors': [a, b], 'single_contracts': len(singles[s]),
                       'paired_contracts': len(doubles[s]), 'matchings_checked': layout_count,
                       'matchings_requiring_paired_branch': pair_count, 'contracts': contracts})
    return {'classification': 'TWO_STAGE_PROGRESS_TO_ONE_OMITTED_CORE_VERTEX',
            'source': 'D0099.conf', 'source_sha256': sha256(raw).hexdigest(),
            'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
            'attribution': 'Yuta Inoue catalogue, MIT; Gonthier/Emery Kempe closure and trace alignment.',
            'initial_inputs': initial, 'intermediate_forms': 5,
            'single_contracts': sum(map(len, singles)), 'paired_contracts': sum(map(len, doubles)),
            'matching_layouts_independently_checked': sum(s['matchings_checked'] for s in stages),
            'stages': stages, 'stored_interior_colourings': 0,
            'lean_strategy_sha256': sha256(path.read_bytes()).hexdigest(),
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
            'limits': ['One core vertex can remain uncoloured; this is not a full repair or strict ambient reduction.',
                       'Two stages count refreshed matching queries, not physical component switches.',
                       'The actual-graph theorem uses Kempe closure of that same exterior; no arbitrary physical history-length bound is proved.',
                       'Initial minimum-hole counts and matching census are independent program checks.',
                       'No geometric supply, universal coverage or catalogue deletion is established.']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    payload = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
