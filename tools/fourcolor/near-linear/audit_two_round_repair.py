#!/usr/bin/env python3
"""Replay a nonmonotone two-round repair and test proposed progress measures.

The source repair and bounded chromogram inverse are Lean checked. Relation
profiles and the census here are independent program evidence. Adversarial
matchings need not arise together from one physical exterior.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip, interval_possible
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_majority_repair import accepted, policies
from audit_two_port_core import eliminate
from generate_exceptional_repair import boundary, pairings, traces


def profile(g, w):
    colouring, result = eliminate(g, len(w), boundary(w))
    sizes = tuple(len(stage['kept_relation']) for stage in result['stages'])
    sizes += (len(result['terminal_pairs']),)
    require((colouring is None) == (complete_patch(g, boundary(w)) is None),
            'Elimination and independent extension disagree')
    return colouring is not None, sizes


def matching(w, fixed, mate):
    require(len(mate) == len(w) and all(0 <= j < len(w) for j in mate), 'Matching carrier differs')
    require(all(mate[mate[i]] == i and ((mate[i] == i) == (w[i] == fixed))
                for i in range(len(w))), 'Not an active-port involution')
    pairs = [(i, j) for i, j in enumerate(mate) if i < j]
    require(not any(a < c < b < d or c < a < d < b for a, b in pairs for c, d in pairs),
            'Matching crosses')
    return pairs


def witness(g, w, colours):
    require(len(colours) == len(g) and all(c in range(4) for c in colours), 'Colour carrier differs')
    require(all(colours[u] != colours[v] for u, ns in enumerate(g) for v in ns), 'Improper colouring')
    require(tuple(colours[i] ^ colours[(i+1) % len(w)] for i in range(len(w))) == tuple(w),
            'Boundary trace differs')


def example(here, g):
    data = json.loads((here / 'two-round-repair-example.json').read_text())
    require(data['source']['sha256'] == sha256((here / data['source']['file']).read_bytes()).hexdigest(),
            'Fixture source pin differs')
    w = tuple(data['word'])
    ok, sizes = profile(g, w)
    require(not ok and list(sizes) == data['sizes'], 'Initial profile differs')
    require({r['fixed'] for r in data['responses']} == {1, 2, 3}, 'A fixed colour is missing')
    switches = 0
    for r in data['responses']:
        pairs = matching(w, r['fixed'], r['mate'])
        require([list(p) for p in pairs] == r['pairs'], 'Recorded components differ')
        require(len(pairs) == len(r['answers']), 'Missing chord response')
        for pair, answer in zip(pairs, r['answers']):
            changed = flip(w, r['fixed'], [pair])
            extends, result = profile(g, changed)
            require(list(changed) == answer['word'] and list(result) == answer['sizes'], 'Answer differs')
            require(not extends and all(a <= b for a, b in zip(result, sizes)),
                    'The response improves a relation size or extends directly')
            switches += 1
    slots = [i for i, c in enumerate(w) if c != 3]
    possible = {slots[next(b if a == slots.index(9) else a for a, b in m
                           if slots.index(9) in (a, b))] for m in pairings(len(slots))}
    require(possible == {row['partner'] for row in data['strategy']}, 'First-stage partner set differs')
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripTwoRoundRepair.lean'
    text = lean.read_text()
    input_text = re.search(r'def input : List Color := \[([^\]]+)\]', text)[1]
    require(tuple(map(int, re.findall(r'c([0-3])', input_text))) == w, 'Lean input differs')
    raw = re.search(r'def data : String := "([0-3]+)"', text)[1]
    chunks = [list(map(int, raw[i:i+19])) for i in range(0, len(raw), 19)]
    direct = []
    intermediate = None
    for row in data['strategy']:
        changed = flip(w, 3, [(9, row['partner'])])
        extends, result = profile(g, changed)
        require(list(changed) == row['word'] and list(result) == row['sizes'], 'First-stage answer differs')
        if row['colouring']:
            require(extends, 'Direct answer does not extend')
            witness(g, changed, row['colouring'])
            direct.append(row['colouring'])
        else:
            require(not extends and intermediate is None, 'Indirect answer differs')
            intermediate = row
            require(row['second_repairs'], 'Missing second-stage repair')
            for repair in row['second_repairs']:
                active = [i for i, c in enumerate(changed) if c != repair['fixed']]
                block = repair['block']
                k = active.index(block[0])
                require(block == [active[(k+j) % len(active)] for j in range(len(block))], 'Block not cyclic')
                require(len(active) < 2*len(block), 'Not a majority block')
                require(repair['pairs'] == [list(p) for p in zip(block, block[1:])], 'Not adjacent choices')
                require(len(repair['pairs']) == len(repair['colourings']), 'Missing second-stage witness')
                for pair, colours in zip(repair['pairs'], repair['colourings']):
                    witness(g, flip(changed, repair['fixed'], [pair]), colours)
    require(direct == chunks and len(raw) == 76 and intermediate is not None, 'Lean witness data differs')
    require(intermediate['word'] == [1,1,1,2,1,2,3,2,2,2,1], 'Existing majority input differs')
    return {'input': w, 'profile': sizes, 'nonimproving_chord_responses': switches,
            'independent_adversarial_matchings': 3, 'direct_first_stage_answers': len(direct),
            'indirect_first_stage_answers': 1, 'intermediate_profile': intermediate['sizes'],
            'new_lean_colour_witness_bytes': len(raw),
            'fixture_sha256': sha256((here / 'two-round-repair-example.json').read_bytes()).hexdigest()}


def census(g):
    words = traces(11)
    _, cache = policies(words)
    profiles, base = [], set()
    for i, w in enumerate(words):
        extends, sizes = profile(g, w)
        if extends:
            base.add(i)
        colours = boundary(w)
        unary = tuple(len(set(range(4)) - {colours[x] for x in g[v] if x < 11}) for v in range(11, 19))
        profiles.append((sizes, unary))
    first = base | {i for i, row in enumerate(cache) if accepted(row, base, 'majority')}
    measures = {
        'first_empty': lambda s, u: next((i for i, x in enumerate(s) if x == 0), len(s)),
        'nonempty_count': lambda s, u: sum(x > 0 for x in s),
        'sum_relations': lambda s, u: sum(s),
        'lex_relations': lambda s, u: s,
        'reverse_lex_relations': lambda s, u: s[::-1],
        'lex_unary_then_relations': lambda s, u: u+s,
        'lex_relations_then_unary': lambda s, u: s+u,
        'sum_unary_then_relations': lambda s, u: (sum(u), sum(s))}
    results = []
    for name, measure in measures.items():
        ranks = [measure(*p) for p in profiles]
        failed = []
        for i, row in enumerate(cache):
            if i in first:
                continue
            improves = lambda j: j in first or ranks[j] > ranks[i]
            progress = False
            for slots, pairs, _, _ in row:
                bad = {pair for pair, j in pairs.items() if not improves(j)}
                if not interval_possible(slots, bad):
                    progress = True
                    break
            if not progress:
                failed.append(i)
        results.append({'measure': name, 'failures': len(failed), 'first_failure': words[failed[0]]})
    require(len(words) == 7381 and len(base) == 1587 and len(first) == 1936, 'Census domain changed')
    require([r['failures'] for r in results] == [1694,1694,1419,1368,1200,897,1070,902],
            'Progress census differs')
    return {'canonical_inputs': len(words), 'direct_inputs': len(base), 'one_majority_round_inputs': len(first),
            'unresolved_inputs_tested': len(words)-len(first), 'measures': results,
            'criterion': 'Choose a fixed colour; every noncrossing matching must contain a single chord whose answer is in the initial set or strictly increases the stated measure.'}


def verify(here):
    source = (here / 'D0099.conf').read_bytes()
    require(sha256(source).hexdigest() == '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Pinned catalogue source differs')
    n, g = graph(source)
    require(n == 11 and len(g) == 19, 'Source carrier differs')
    return {'evidence': 'Source repair and inverse bridge: Lean; profiles and census: independent program.',
            'source_sha256': sha256(source).hexdigest(), 'example': example(here, g), 'census': census(g),
            'limits': ['The adversarial matchings are separate abstract responses; one physical exterior realizing them together is not constructed.',
                       'No impossibility of general history-dependent or multi-component repair is proved.',
                       'The finite inverse covers two inputs, not arbitrary boundary widths.',
                       'No full-source reducibility, geometric supply, strict reduction or catalogue compression is established.'],
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2)+'\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
