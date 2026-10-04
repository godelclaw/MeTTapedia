#!/usr/bin/env python3
"""Test the majority-block rule and its composition with anchor repairs.

Lean proves majority selection and two exact source consumers. The full
D0099 closures and the bounded converse test below are program evidence.
No table of source strategies or matching signatures is exported.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip, interval_possible
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_parent_fan import direct_words
from generate_exceptional_repair import canonical, pairings, traces


def half_run(bits):
    n = len(bits)
    return n > 0 and any(all(bits[(i+j) % n] for j in range(n // 2)) for i in range(n))


def blocker_test():
    results = []
    for n in range(2, 15, 2):
        matchings = pairings(n)
        ear_masks = []
        for matching in matchings:
            mask = 0
            for a, b in matching:
                if b == a + 1:
                    mask |= 1 << a
                if a == 0 and b == n-1:
                    mask |= 1 << (n-1)
            ear_masks.append(mask)
        for mask in range(1 << n):
            hit = all(mask & ears for ears in ear_masks)
            require(hit == half_run([bool(mask >> i & 1) for i in range(n)]),
                    'Bounded ear-blocker characterization differs')
        results.append({'active_ports': n, 'subsets_checked': 1 << n,
                        'noncrossing_matchings': len(matchings)})
    return results


def policies(words):
    index = {w: i for i, w in enumerate(words)}
    cache = []
    for w in words:
        row = []
        for fixed in (1, 2, 3):
            slots = [i for i, c in enumerate(w) if c != fixed]
            pairs = {(a, b): index[canonical(flip(w, fixed, [(a, b)]))]
                     for i, a in enumerate(slots) for j, b in enumerate(slots) if (i-j) % 2}
            anchors = [set(pairs[a, b] for b in slots if (a, b) in pairs) for a in slots]
            ears = [pairs[a, slots[(i+1) % len(slots)]] for i, a in enumerate(slots)]
            row.append((slots, pairs, anchors, ears))
        cache.append(row)
    return index, cache


def accepted(row, known, mode):
    for slots, pairs, anchors, ears in row:
        if mode in ('anchor', 'combined') and any(a and a <= known for a in anchors):
            return True
        if mode == 'anchor':
            continue
        bits = [v in known for v in ears]
        majority = half_run(bits)
        good = {tuple(sorted((slots[i], slots[(i+1) % len(slots)])))
                for i, ok in enumerate(bits) if ok}
        bad = {pair for pair in pairs if tuple(sorted(pair)) not in good}
        interval = not interval_possible(slots, bad)
        require(majority == interval, 'Majority and interval tests disagree on a source query')
        if majority:
            return True
    return False


def close(initial, cache, mode):
    known = set(initial)
    stages = [len(known)]
    while True:
        new = {i for i, row in enumerate(cache) if i not in known and accepted(row, known, mode)}
        if not new:
            return known, stages
        known |= new
        stages.append(len(known))


def phase_closure(initial, cache, first):
    known = set(initial)
    phases = []
    modes = ('anchor', 'majority') if first == 'anchor' else ('majority', 'anchor')
    while True:
        old = len(known)
        for mode in modes:
            known, stages = close(known, cache, mode)
            phases.append({'rule': mode, 'start': stages[0], 'end': stages[-1],
                           'rounds': len(stages)-1})
        if len(known) == old or len(known) == len(cache):
            return phases


def consumers(here):
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripMajorityRepair.lean'
    text = lean.read_text()
    examples = json.loads((here / 'adaptive-chords-audit.json').read_text())['kernel_consumers']
    block = text.split('def embed', 1)[1].split('def rank', 1)[0]
    results = []
    for example in examples:
        side = example['side']
        order = list(map(int, re.search(rf'\| {side} => !\[([^\]]+)\]', block)[1].split(',')))
        require(set(order) == set(example['active_positions']), 'Active order differs')
        good = {tuple(pair) for pair in example['successful_pairs']}
        require(all(tuple(sorted((order[i], order[i+1]))) in good for i in range(3)),
                'The majority block has an uncertified adjacent pair')
        results.append({'side': side, 'active_order': order,
                        'block': order[:4], 'active_ports': 6, 'block_ports': 4,
                        'successful_adjacent_pairs': [sorted((order[i], order[i+1])) for i in range(3)]})
    return results


def seed_test(index, cache, initial):
    words = [tuple(map(int, text)) for text in
             ('12322212313', '12322223131', '12323211232', '12323321221', '12332132221')]
    seeds = {index[w] for w in words}
    require(len(seeds) == 5 and not seeds & initial, 'Seed domain differs')
    require(all(accepted(cache[i], initial, 'majority') for i in seeds),
            'A seed needs more than one majority step')
    known, stages = close(initial | seeds, cache, 'anchor')
    require(len(known) == len(cache), 'Five seeds do not generate full anchor closure')
    removals = [len(close(initial | (seeds - {index[w]}), cache, 'anchor')[0]) for w in words]
    require(removals == [2305, 2059, 2271, 2260, 6661], 'Seed removal census differs')
    return {'words': words, 'each_is_a_single_majority_step': True, 'anchor_stages': stages,
            'coverage_with_each_seed_removed': removals,
            'candidate_anchor_implications_before_deduplication':
                sum(bool(support) for row in cache for _, _, anchors, _ in row for support in anchors),
            'scope': 'A sufficient irredundant set found by greedy search, not a global minimum. These five repairs and the ensuing full closure are not Lean certified here.'}


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() == '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Pinned source differs')
    n, g = graph(raw)
    words = traces(n)
    index, cache = policies(words)
    initial = {index[w] for w in direct_words(g, words)}
    results = []
    for mode in ('anchor', 'majority', 'combined'):
        known, stages = close(initial, cache, mode)
        results.append({'rule': mode, 'stages': stages, 'remaining': len(words)-len(known)})
    require([r['stages'][-1] for r in results] == [1993, 2251, 7381], 'Repair census differs')
    require(len(results[-1]['stages']) == 15, 'Combined round count differs')
    first = initial | {i for i, row in enumerate(cache) if accepted(row, initial, 'majority')}
    seeded, seeded_stages = close(first, cache, 'anchor')
    require(len(first) == 1936 and len(seeded) == len(words), 'First-round seed census differs')
    return {'evidence': 'General majority theorem and two source repairs are Lean checked; all source closures below are program evidence.',
            'source_sha256': sha256(raw).hexdigest(),
            'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
            'attribution': 'Yuta Inoue, 2026, MIT licence; Gonthier/Emery chromogram semantics.',
            'canonical_inputs': len(words), 'direct_source_inputs': len(initial),
            'policies': results, 'phase_experiments': {first: phase_closure(initial, cache, first)
                                                     for first in ('anchor', 'majority')},
            'one_majority_round_then_anchors': {'new_majority_inputs': len(first)-len(initial),
                                               'anchor_stages': seeded_stages},
            'five_seed_experiment': seed_test(index, cache, initial),
            'bounded_blocker_equivalence': blocker_test(), 'kernel_consumers': consumers(here),
            'limits': ['The general theorem is a sufficient majority condition; its converse is only tested through fourteen active ports.',
                      'The 7381-input closure is not a Lean proof or a compact progress-rank theorem.',
                      'Both source consumers still require a supplied noncrossing matching; no inverse chromogram decoder is supplied.',
                      'No geometric supply, strict reduction or classical certificate dependency is removed.'],
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
