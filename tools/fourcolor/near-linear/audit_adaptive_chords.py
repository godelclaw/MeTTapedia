#!/usr/bin/env python3
"""Compare repair policies and replay two adaptive interval consumers.

Full game closures and the observation minimum are program evidence only.
Lean proves the uniform interval law and the two stated matching consumers.
"""
import argparse
from collections import defaultdict
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_strip_parent_fan import parents, direct_words, trace
from generate_exceptional_repair import boundary, canonical, pairings, traces


def flip(w, fixed, pairs):
    x = list(w)
    for a, b in pairs:
        x[a] ^= fixed
        x[b] ^= fixed
    return tuple(x)


def interval_possible(ports, bad):
    @lru_cache(None)
    def rec(lo, n):
        if n == 0:
            return True
        return any((ports[lo], ports[lo+k]) in bad and rec(lo+1, k-1) and
                   rec(lo+k+1, n-k-1) for k in range(1, n, 2))
    return rec(0, len(ports))


def policy_cache(words):
    index = {w: i for i, w in enumerate(words)}
    rows = []
    for w in words:
        row = []
        for fixed in (1, 2, 3):
            slots = [i for i, c in enumerate(w) if c != fixed]
            edge = {(a, b): index[canonical(flip(w, fixed, [(a, b)]))]
                    for i, a in enumerate(slots) for j, b in enumerate(slots) if (i-j) % 2}
            anchored = [set(edge[a, b] for b in slots if (a, b) in edge) for a in slots]
            matchings, unions = [], []
            for skeleton in pairings(len(slots)):
                actual = [(slots[a], slots[b]) for a, b in skeleton]
                single = {edge[a, b] for a, b in actual}
                double = {index[canonical(flip(w, fixed, selected))]
                          for selected in combinations(actual, 2)}
                matchings.append(single)
                unions.append(single | double)
            grid = [[edge[a, b] for b in slots[1::2]] for a in slots[::2]]
            row.append((slots, edge, anchored, matchings, unions, grid))
        rows.append(row)
    return index, rows


def hall_defect(grid, known):
    neighbors = [sum(1 << j for j, v in enumerate(row) if v not in known) for row in grid]
    for subset in range(1, 1 << len(grid)):
        union = 0
        for i, ns in enumerate(neighbors):
            if subset >> i & 1:
                union |= ns
        if union.bit_count() < subset.bit_count():
            return True
    return False


def accepted(row, known, mode):
    for slots, edge, anchored, matchings, unions, grid in row:
        if mode == 'anchored':
            if any(a and a <= known for a in anchored):
                return True
        elif mode == 'hall':
            if hall_defect(grid, known):
                return True
        elif mode == 'adaptive':
            bad = {pair for pair, answer in edge.items() if answer not in known}
            good = not interval_possible(slots, bad)
            require(good == all(bool(ms & known) for ms in matchings),
                    'Interval recurrence differs from independent matching enumeration')
            if good:
                return True
        elif mode == 'two_chords':
            if all(bool(ms & known) for ms in unions):
                return True
        else:
            raise ValueError(mode)
    return False


def close(initial, words, index, cache, mode):
    known = {index[w] for w in initial}
    stages = [len(known)]
    while len(known) < len(words):
        new = {i for i, row in enumerate(cache) if i not in known and accepted(row, known, mode)}
        if not new:
            break
        known |= new
        stages.append(len(known))
    return {words[i] for i in known}, stages


def transport(words, ps, winning):
    sets = [set(), set()]
    for w in words:
        colours = boundary(w)
        for i, p in enumerate(ps):
            slot = p['omitted']
            for c in set(range(4)) - {colours[slot-1], colours[slot], colours[(slot+1) % len(w)]}:
                old = colours.copy()
                old[slot] = c
                if canonical(trace(old)) in winning[i]:
                    sets[i].add(w)
                    break
    return sets


def observation_minimum(words, direct, parent_sets):
    only = [sorted((parent_sets[i] - parent_sets[1-i]) - direct) for i in (0, 1)]
    def observation(w, positions):
        palette = {}
        return tuple(palette.setdefault(w[i], len(palette)) for i in positions)
    def conflict(positions):
        left = {observation(w, positions): w for w in only[0]}
        for w in only[1]:
            key = observation(w, positions)
            if key in left:
                return [left[key], w]
        return None
    layers, sufficient = [], []
    for width in range(1, 12):
        sufficient = [pos for pos in combinations(range(11), width) if conflict(pos) is None]
        layers.append({'observed_edges': width, 'sufficient_subsets': len(sufficient)})
        if sufficient:
            break
    seams = (6, 7, 10, 0)
    classes = defaultdict(list)
    for side in (0, 1):
        for w in only[side]:
            classes[observation(w, seams)].append(side)
    require(sufficient == [(0,1,2,3,6,7,8,9,10)], 'Observation minimum changed')
    require(all(set(sides) == {0,1} for sides in classes.values()) and len(classes) == 14,
            'Seam ambiguity changed')
    return {'exclusive_parent_inputs': list(map(len, only)), 'layers': layers,
            'minimal_sufficient_edge_subsets': sufficient, 'seam_pattern_classes': len(classes),
            'all_seam_classes_ambiguous': True, 'seam_counterexample': conflict(seams),
            'scope': 'Nonadaptive choice between the computed parent winning sets, excluding direct source inputs; fixed subsets of edge colours observed up to one common palette permutation.'}


def source_examples(here, adj):
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripIntervalRepair.lean'
    text = lean.read_text()
    def block(name):
        return re.search(rf'^def {name}\b(.*?)(?=^\S)', text, re.M | re.S)[1]
    results = []
    for tag in ('false', 'true'):
        word = tuple(map(int, re.findall(r'c([0-3])',
            re.search(rf'\| {tag} => !\[([^\]]+)\]', block('word'))[1])))
        ps = [tuple(map(int, p)) for p in re.findall(r'\((\d+),(\d+)\)',
            re.search(rf'\| {tag} => \[([^\]]+)\]', block('pairs'))[1])]
        raw = re.search(rf'\| {tag} => "([0-3]+)"', block('data'))[1]
        require(len(raw) == 76 and len(ps) == 4, 'Source witness dimensions differ')
        for i, pair in enumerate(ps):
            colours = list(map(int, raw[19*i:19*(i+1)]))
            require(all(colours[u] != colours[v] for u, ns in enumerate(adj) for v in ns),
                    'An actual source witness is improper')
            require(trace(colours[:11]) == flip(word, 1, [pair]), 'Answer trace differs')
        slots = [i for i, c in enumerate(word) if c != 1]
        good = set(ps) | {(b, a) for a, b in ps}
        bad = {(a,b) for a in slots for b in slots if a != b and (a,b) not in good}
        require(not interval_possible(slots, bad), 'Bad chords admit a noncrossing matching')
        require(complete_patch(adj, boundary(word)) is None, 'Input already extends')
        # Certify all opposite-parity choices against actual extension as an independent check.
        for i,a in enumerate(slots):
            for j,b in enumerate(slots):
                if (i-j) % 2:
                    require((complete_patch(adj, boundary(flip(word,1,[(a,b)]))) is not None) ==
                            ((a,b) in good), 'The supplied good-pair set is not exact')
        results.append({'side':tag,'word':word,'active_positions':slots,'successful_pairs':ps,
                        'source_witness_bytes':len(raw),'input_nonextension_program_checked':True,
                        'good_pairs_exact_for_direct_extension':True})
    return results


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    r, adj = graph(raw)
    ps = parents(adj)
    words = traces(r)
    index, cache = policy_cache(words)
    direct = [direct_words(g, words) for g in [adj] + [p['graph'] for p in ps]]
    results, final_parent_sets = [], None
    for mode in ('anchored', 'hall', 'adaptive', 'two_chords'):
        computed = [close(d, words, index, cache, mode) for d in direct]
        transported = transport(words, ps, [x[0] for x in computed[1:]])
        base = direct[0] | transported[0] | transported[1]
        combined, stages = close(base, words, index, cache, mode)
        results.append({'policy':mode,'source_stages':computed[0][1],
                        'parent_stages':[x[1] for x in computed[1:]], 'combined_stages':stages,
                        'remaining_source_inputs':len(words)-len(combined)})
        if mode == 'two_chords':
            final_parent_sets = transported
    require([r['remaining_source_inputs'] for r in results] == [5344,1200,0,0], 'Policy comparison differs')
    return {'evidence':'General interval theorem and two source consumers Lean checked; full closure and observation results are independent program evidence.',
            'source_sha256':sha256(raw).hexdigest(),'catalogue_revision':'c2ce7a96e35256201526e2abb51a39d04a588b53',
            'attribution':'Yuta Inoue, 2026, MIT licence; Gonthier/Emery chromogram semantics.',
            'canonical_inputs':len(words),'policies':results,
            'parent_selection_observations':observation_minimum(words,direct[0],final_parent_sets),
            'kernel_consumers':source_examples(here,adj),
            'limits':['Full D0099 repair and the parent fixed points are not Lean certified here.',
                      'The observation minimum does not bound symbolic summaries, adaptive inspection or other repair strategies.',
                      'Two-round combined repair uses substantial parent strategies; it is not a total depth or cost bound.',
                      'No geometric occurrence supply, strict reduction or catalogue compression follows.'],
            'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
