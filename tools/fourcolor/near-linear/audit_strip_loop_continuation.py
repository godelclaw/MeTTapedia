#!/usr/bin/env python3
"""Cross-check the four-stage joint repair and a bounded conflict-size test.

Lean proves the matching composition and both same-exterior loop repairs.
The complete-source game and conflict-size thresholds are program evidence.
No all-boundary strategy or source-colouring table is exported.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_partial import partial
from audit_triangle_strip_lists import PINS, propagate, reconstruct
from generate_exceptional_repair import boundary, canonical, pairings, traces


def phase_test(ring, g):
    words = traces(ring)
    index = {w: i for i, w in enumerate(words)}
    core = set(range(len(g) - ring))
    sizes = []
    for w in words:
        b = boundary(w)
        if partial(g, ring, b, []) is not None:
            sizes.append(0)
            continue
        sizes.append(next(k for k in range(1, len(core)+1)
            if any(partial(g, ring, b, core-set(s)) is None
                   for s in combinations(sorted(core), k))))
    responses = []
    for i, w in enumerate(words):
        queries = []
        for fixed in (1, 2, 3):
            slots = [j for j, c in enumerate(w) if c != fixed]
            rows = []
            for matching in pairings(len(slots)):
                cs = [(slots[a], slots[b]) for a, b in matching]
                rows.append({i} | {index[canonical(flip(w, fixed, chosen))]
                    for k in range(1, len(cs)+1) for chosen in combinations(cs, k)})
            queries.append(rows)
        responses.append(queries)
    tests = []
    for limit in (3, 4, 7):
        domain = {i for i, s in enumerate(sizes) if s <= limit}
        known = {i for i, s in enumerate(sizes) if s == 0}
        layers = [len(known)]
        while True:
            new = {i for i in domain-known
                   if any(all(row & known for row in query) for query in responses[i])}
            if not new:
                break
            known |= new
            layers.append(len(known))
        tests.append(dict(maximum_smallest_conflict=limit, domain=len(domain),
                          layers=layers, unresolved=len(domain-known)))
    require([(t['domain'], t['unresolved']) for t in tests] ==
            [(1769, 81), (2247, 0), (2461, 0)], 'Conflict-size phase census differs')
    return dict(canonical_inputs=len(words), smallest_conflict_histogram=dict(Counter(sizes)),
                tests=tests,
                scope='Abstract matching game: each round selects a colour pair and a subset of one supplied noncrossing matching. Adverse responses from different rounds or queries are not asserted to coexist in a physical exterior.',
                interpretation='Keeping the smallest conflicting core at size at most three can trap the game; size at most four suffices for every input in that bounded domain. This is not a monotone rank or an unbounded-family theorem.')


def verify(here):
    raw = (here / 'D0063.conf').read_bytes()
    require(sha256(raw).hexdigest() == PINS['D0063'], 'Source pin differs')
    ring, g = graph(raw)
    src = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    text = (src / 'StripLoopContinuation.lean').read_text()
    word_text = text.split('def word ', 1)[1].split('def palette', 1)[0]
    words = [tuple(map(int, re.findall(r'c([1-3])', row)))
             for row in re.findall(r'!\[([^!\[\]]+)\]', word_text)]
    require([''.join(map(str, w)) for w in words] ==
            ['1111223333', '1222222221', '1222332221', '1222331112'], 'Stage words differ')
    perms = re.findall(r'\.e([123]{3})', text.split('def palette', 1)[1].split('def colour', 1)[0])
    require(perms == ['321', '321', '123', '321'], 'Stage palettes differ')
    selector = (src / 'StripLoopMatching.lean').read_text()
    good = [tuple(map(int, p)) for p in re.findall(r'\((\d+),(\d+)\)',
        selector.split('def good ', 1)[1].split('instance', 1)[0])]
    singles = [[(0,1), (1,2), (2,3)], good, [(3,4), (4,5), (5,6), (6,7)],
               [(8,9), (9,0), (1,2), (3,6)]]
    doubles = [[], [((0,5), (1,2))], [], [((8,7), (9,6)), ((9,2), (0,1))]]
    edges = [(v, u) for v in range(7) for u in range(7) if ring+u in g[ring+v]]
    result = []
    for s, (w, perm) in enumerate(zip(words, perms)):
        c = tuple(int(perm[a-1]) for a in w)
        contracts = [[p] for p in singles[s]] + [list(ps) for ps in doubles[s]]
        direct, earlier = 0, []
        for ps in contracts:
            et = flip(c, 1, ps)
            normalized = canonical(et)
            if normalized in words[:s]:
                earlier.append(words.index(normalized))
                continue
            b = boundary(et)
            lists = [set(range(4)) - {b[u] for u in g[ring+v] if u < ring} for v in range(7)]
            for choice in product(range(4), repeat=2):
                guard, steps = propagate(lists, (1,3), choice, edges)
                if guard is not None and steps <= 4:
                    reconstruct(g, ring, b, (1,3), choice, guard)
                    break
            else:
                raise AssertionError('A terminal source contract has no forest guard')
            direct += 1
        slots = [i for i, a in enumerate(c) if a != 1]
        for m in pairings(len(slots)):
            components = {tuple(sorted((slots[a], slots[b]))) for a, b in m}
            require(any(all(tuple(sorted(p)) in components for p in ps) for ps in contracts),
                    'A matching has no compatible successful component batch')
        result.append(dict(stage=s, word=''.join(map(str,w)), active_ports=len(slots),
                           matching_crosschecks=len(pairings(len(slots))),
                           direct_forest_contracts=direct, earlier_stage_references=earlier))
    require(sum(r['direct_forest_contracts'] for r in result) == 20, 'Terminal count differs')
    require(sum(len(r['earlier_stage_references']) for r in result) == 3, 'Continuation count differs')
    return dict(classification='CHECKED_COMPOSED_LOOP_REPAIR_WITH_PROGRAM_PHASE_TEST',
                catalogue_revision='c2ce7a96e35256201526e2abb51a39d04a588b53',
                source_sha256=PINS['D0063'], stages=result,
                total_matching_crosschecks=sum(r['matching_crosschecks'] for r in result),
                phase_test_program_only=phase_test(ring, g),
                matching_layout_table_exported=False, source_colouring_table_exported=False,
                source_guard_search_domain=16, source_guard_sweeps=4,
                all_input_reducibility_kernel_claimed=False, new_coverage_entries_removed=0,
                new_original_certificates_removed=0,
                lean_sources={p.name: sha256(p.read_bytes()).hexdigest() for p in
                    [src/'KempeShortBlock.lean', src/'StripLoopMatching.lean', src/'StripLoopContinuation.lean']})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
