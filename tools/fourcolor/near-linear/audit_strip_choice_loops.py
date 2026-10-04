#!/usr/bin/env python3
"""Replay conditional colour loops and their first majority repair.

The critical-input census and one-query tests are bounded program evidence.
The two implication obstructions and the first input's same-exterior repair
are separately proved in Lean. No closure strategy table is saved.
"""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_partial import partial
from audit_triangle_strip_lists import PINS, propagate, reconstruct, supported
from generate_exceptional_repair import boundary, canonical, pairings, traces


def census(here, name):
    ring, g = graph((here / (name + '.conf')).read_bytes())
    n = len(g) - ring
    critical = []
    for word in traces(ring):
        b = boundary(word)
        if partial(g, ring, b, []) is None and all(
                partial(g, ring, b, [h]) is not None for h in range(n)):
            critical.append(word)
    successes = {1: [], 2: [], 'all': []}
    for word in critical:
        wins = {k: False for k in successes}
        for fixed in (1, 2, 3):
            slots = [i for i, c in enumerate(word) if c != fixed]
            cached = {}

            def extends(chords):
                out = canonical(flip(word, fixed, chords))
                if out not in cached:
                    cached[out] = partial(g, ring, boundary(out), []) is not None
                return cached[out]

            for limit in wins:
                if wins[limit]:
                    continue
                k = len(slots) // 2 if limit == 'all' else limit
                wins[limit] = all(any(extends(chosen)
                    for width in range(1, min(k, len(m)) + 1)
                    for chosen in combinations([(slots[a], slots[b]) for a, b in m], width))
                    for m in pairings(len(slots)))
        for k, win in wins.items():
            if win:
                successes[k].append(''.join(map(str, word)))
    return dict(source=name, canonical_inputs=len(traces(ring)),
                minimal_nonextension_inputs=len(critical),
                one_query_single_component=len(successes[1]),
                one_query_two_components=len(successes[2]),
                one_query_arbitrary_batch=len(successes['all']))


def verify(here):
    for name, pin in PINS.items():
        require(sha256((here / (name + '.conf')).read_bytes()).hexdigest() == pin,
                'Source pin differs')
    src = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    text = (src / 'StripChoiceLoops.lean').read_text()

    def block(name, end):
        return text.split('def ' + name + ' ', 1)[1].split(end, 1)[0]

    boundaries = [tuple(map(int, re.findall(r'c([0-3])', line)))
                  for line in block('boundary', 'def ProperBoundary').splitlines() if '=>' in line]
    forward = [[tuple(map(int, p)) for p in re.findall(r'\((\d+),c([0-3])\)', line)]
               for line in block('forward', 'def backward').splitlines() if '=>' in line]
    backward = [[tuple(map(int, p)) for p in re.findall(r'\((\d+),c([0-3])\)', line)]
                for line in block('backward', 'theorem forward_steps').splitlines() if '=>' in line]
    require(len(boundaries) == len(forward) == len(backward) == 2, 'Loop case count differs')
    ring, g = graph((here / 'D0063.conf').read_bytes())
    edges = [(v, u) for v in range(7) for u in range(7) if u + ring in g[v + ring]]
    loops = []
    for b, fp, bp in zip(boundaries, forward, backward):
        lists = [set(range(4)) - {b[u] for u in g[ring + v] if u < ring} for v in range(7)]
        require(len(lists[6]) == 1 and (6, 3) in edges, 'Initial propagation differs')
        lists[3] -= lists[6]
        require(all(lists) and supported(lists, edges), 'Residual lists lack local support')
        require(lists[0] == {0, 1}, 'The pivot does not have two choices')
        require(fp[0] == bp[-1] == (0, 0) and fp[-1] == bp[0] == (0, 1),
                'Implication endpoints differ')
        for path in (fp, bp):
            for (v, a), (u, c) in zip(path, path[1:]):
                require((v, u) in edges and lists[u] - {a} <= {c},
                        'Unsound local colour implication')
        require(partial(g, ring, b, []) is None, 'The forbidden source extends')
        require(all(partial(g, ring, b, [v]) is not None for v in range(7)),
                'A proper core deletion still fails')
        loops.append(dict(boundary=b, residual_lists=[sorted(s) for s in lists],
                          implication_lengths=[len(fp)-1, len(bp)-1],
                          every_single_core_deletion_extends_program_checked=True))

    repair = (src / 'StripChoiceLoopRepair.lean').read_text()
    word_text = repair.split('def word ', 1)[1].split('def colour', 1)[0]
    word = tuple(map(int, re.findall(r'c([0-3])', word_text)))
    require(word == tuple(b ^ boundaries[0][(i+1) % ring]
                          for i, b in enumerate(boundaries[0])), 'Repair input differs')
    coloured = tuple({1: 3, 2: 2, 3: 1}[a] for a in word)
    choices = list(map(int, re.findall(r'c([0-3])',
        repair.split('def choice ', 1)[1].split('theorem guarded_answers', 1)[0])))
    require(len(choices) == 8, 'Joint anchor data size differs')
    for index in range(4):
        b = boundary(flip(coloured, 1, [(index+1, index+2)]))
        lists = [set(range(4)) - {b[u] for u in g[ring + v] if u < ring} for v in range(7)]
        choice = choices[2*index:2*index+2]
        result, steps = propagate(lists, (1, 3), choice, edges)
        require(result is not None and steps <= 2, 'Repair forest guard failed')
        reconstruct(g, ring, b, (1, 3), choice, result)
    slots = [i for i, c in enumerate(coloured) if c != 1]
    good = {(i, i+1) for i in range(1, 5)}
    require(len(slots) == 8, 'Active ring differs')
    for matching in pairings(len(slots)):
        require(any((slots[a], slots[b]) in good for a, b in matching),
                'Matching avoids the majority block')
    rows = [census(here, name) for name in PINS]
    require([(r['minimal_nonextension_inputs'], r['one_query_arbitrary_batch']) for r in rows]
            == [(4, 3), (17, 5), (6, 2)], 'Critical-input census differs')
    return dict(classification='KERNEL_OBSTRUCTIONS_AND_ONE_REPAIR_WITH_PROGRAM_CENSUS',
                catalogue_revision='c2ce7a96e35256201526e2abb51a39d04a588b53',
                loops=loops, successful_reconstruction_guards=4,
                source_anchor_colour_values=8, noncrossing_matchings_checked=len(pairings(8)),
                program_only_critical_census=rows,
                program_scope='Choose one of three colour-pair queries; a fresh adverse noncrossing matching is supplied; choose a batch from that matching. Different queries are not asserted to be simultaneously realized by one physical exterior.',
                full_source_repair_claimed=False, coverage_entries_removed=0,
                original_certificate_dependencies_removed=0, strategy_table_exported=False,
                lean_sources={name: sha256((src / name).read_bytes()).hexdigest()
                              for name in ('StripChoiceLoops.lean', 'StripChoiceLoopRepair.lean')})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
