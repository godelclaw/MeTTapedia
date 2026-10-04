#!/usr/bin/env python3
"""Replay the abstract choice barrier and its composed source repair.

The barrier uses three specified noncrossing matchings, not a demonstrated
physical exterior. The repair handles every noncrossing matching in each
of its four stages and reconstructs complete source witnesses.
"""
import argparse
import ast
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_partial import partial
from generate_exceptional_repair import boundary, canonical, pairings


def definition(text, name):
    found = re.search(rf'^def {name}\b(.*?)(?=^(?:def |theorem |instance |/--|end ))',
                      text, re.M | re.S)
    require(found is not None, f'Missing definition {name}')
    return found[1]


def literal(text):
    return ast.literal_eval(re.sub(r'c([0-3])', r'\1', text).replace('!', '').strip())


def array(text, name):
    return literal(definition(text, name).split(':=', 1)[1])


def rows(text, name):
    data = re.findall(r'^\s*\| (\d+) => (.*?)(?=^\s*\||\Z)',
                      definition(text, name), re.M | re.S)
    require([int(i) for i, _ in data] == list(range(4)), 'Wrong stage indices')
    return [literal(s) for _, s in data]


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82', 'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source carrier differs')
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'

    def witness(word, holes):
        colours = boundary(word)
        require(all(colours[u] != colours[v] for u in range(ring)
                    for v in source[u] if v < ring), 'Improper source boundary')
        f = partial(source, ring, colours, holes)
        if f is None:
            return False
        total = dict(enumerate(colours)) | f
        require(set(total) == set(range(19)) - {ring+h for h in holes}, 'Wrong retained carrier')
        require(all(total[u] != total[v] for u in total for v in source[u] if v in total),
                'Improper reconstructed source witness')
        return True

    def options(word):
        return [h for h in range(8) if witness(word, [h])]

    barrier = (lean / 'StripChoiceBarrier.lean').read_text()
    base = tuple(array(barrier, 'word'))
    require(''.join(map(str, base)) == '11212321221', 'Barrier input differs')
    root_rows, mates = array(barrier, 'roots'), array(barrier, 'mate')
    palettes = re.findall(r'\.e([123]{3})', definition(barrier, 'palette'))
    require(options(base) == [0, 1, 3, 4, 5, 6, 7] and not witness(base, []),
            'Seven-choice nonextension profile differs')
    barrier_rows = []
    for s in range(3):
        perm = [0] + list(map(int, palettes[s]))
        colour = tuple(perm[x] for x in base)
        roots, mate = root_rows[s], mates[s]
        require(all(mate[mate[i]] == i and (mate[i] == i) == (colour[i] == 1)
                    for i in range(ring)), 'Improper matching involution')
        active = [i for i, c in enumerate(colour) if c != 1]
        pairs = [(a, mate[a]) for a in roots]
        require(len({tuple(sorted(p)) for p in pairs}) == len(pairs) and
                sorted(x for p in pairs for x in p) == active, 'Roots do not cover the matching')
        canonical_pairs = sorted(tuple(sorted(p)) for p in pairs)
        require(canonical_pairs in [sorted((active[a], active[b]) for a, b in m)
                                    for m in pairings(len(active))], 'Crossing matching')
        score_counts = Counter()
        orbit = 0
        for mask in range(1 << len(pairs)):
            changed = flip(colour, 1, [p for i, p in enumerate(pairs) if mask >> i & 1])
            answer = tuple(perm[c] for c in changed)
            count = len(options(answer))
            same = canonical(answer) == canonical(base)
            require(same or count < 7, 'A nondecreasing answer escapes the orbit')
            require(not witness(answer, []), 'A barrier answer already extends')
            score_counts[count] += 1
            orbit += same
        barrier_rows.append({'palette': palettes[s], 'pairs': canonical_pairs,
                             'subsets_checked': 1 << len(pairs), 'orbit_answers': orbit,
                             'available_hole_counts': dict(sorted(score_counts.items()))})

    repair = (lean / 'StripChoiceEscape.lean').read_text()
    words, anchors = rows(repair, 'word'), rows(repair, 'anchors')
    singles, doubles = rows(repair, 'singles'), rows(repair, 'doubles')
    palettes = re.findall(r'\.e([123]{3})', definition(repair, 'palette'))
    require(tuple(words[3]) == base, 'The repair does not consume the barrier input')
    stages = []
    for s, word in enumerate(words):
        perm = [0] + list(map(int, palettes[s]))
        c = tuple(perm[x] for x in word)
        require(all(c[a] != 1 for a in anchors[s]), 'Inactive retained anchor')
        direct = 0
        later = set()
        for kind, commands in [('single', singles[s]), ('double', doubles[s])]:
            for cmd in commands:
                if kind == 'single':
                    pairs = [cmd]
                else:
                    r, t, p, q = cmd
                    pairs = [(anchors[s][r], p), (anchors[s][t], q)]
                out = flip(c, 1, pairs)
                previous = next((j for j in range(s) if canonical(out) == canonical(words[j])), None)
                if previous is None:
                    require(witness(out, []), 'Terminal contract does not reconstruct the whole source')
                    direct += 1
                else:
                    later.add(previous)
        active = [i for i, x in enumerate(c) if x != 1]
        single_set = {tuple(sorted(p)) for p in singles[s]}
        matched = 0
        paired = 0
        for matching in pairings(len(active)):
            pairs = [(active[a], active[b]) for a, b in matching]
            mate = {x: y for a, b in pairs for x, y in ((a, b), (b, a))}
            matched += 1
            if any(tuple(sorted(p)) in single_set for p in pairs):
                continue
            require(any(mate[anchors[s][r]] == p and mate[anchors[s][t]] == q
                        for r, t, p, q in doubles[s]), 'Uncovered matching')
            paired += 1
        stages.append({'word': ''.join(map(str, word)), 'anchors': anchors[s],
                       'single_contracts': len(singles[s]), 'paired_contracts': len(doubles[s]),
                       'direct_contracts': direct, 'continuations': sorted(later),
                       'matchings_checked': matched, 'matchings_requiring_pair': paired})
    return {'classification': 'CHOICE_COUNT_GAME_BARRIER_AND_COMPLETE_INPUT_REPAIR',
            'source': 'D0099.conf', 'source_sha256': sha256(raw).hexdigest(),
            'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
            'attribution': 'Yuta Inoue catalogue, MIT; Gonthier/Emery chromogram semantics.',
            'barrier_word': ''.join(map(str, base)), 'available_holes': options(base),
            'barrier_matchings': barrier_rows, 'repair_stages': stages,
            'barrier_subsets_checked': sum(r['subsets_checked'] for r in barrier_rows),
            'repair_matchings_checked': sum(r['matchings_checked'] for r in stages),
            'stored_interior_colourings': 0,
            'lean_sources_sha256': {name: sha256((lean/name).read_bytes()).hexdigest() for name in
                ('KempeAnchorSelection.lean', 'StripChoiceBarrier.lean', 'StripChoiceEscape.lean')},
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
            'limits': ['The barrier is an adversary in the abstract matching game, not one certified exterior graph.',
                       'The repair retains finite contracts for four source inputs, not a complete D0099 repair.',
                       'No physical history-length bound, new strict reduction, geometric supply or catalogue deletion.']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
