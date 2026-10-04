#!/usr/bin/env python3
"""Replay the three-form source guard and its shared short repair strategy.

Each direct answer is reconstructed by ear elimination and cross-checked by
independent colouring search. The Lean proof retains one arbitrary exterior;
this program checks the finite source domains and possible chord replies.
"""
import argparse
from hashlib import sha256
import itertools
import json
from pathlib import Path

from audit_adaptive_chords import flip
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_two_port_core import eliminate
from generate_exceptional_repair import boundary, pairings


def trace(b):
    return tuple(c ^ b[(i+1) % len(b)] for i, c in enumerate(b))


def verify(here):
    source = (here / 'D0099.conf').read_bytes()
    require(sha256(source).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Source pin differs')
    n, g = graph(source)
    require(n == 11 and len(g) == 19, 'Source carrier differs')
    initial = [tuple(map(int, s)) for s in ['11121232111', '11123331111']]
    middle = [tuple(map(int, s)) for s in ['11121232221', '11123331221']]
    residual = tuple(map(int, '11121131111'))
    extra = [tuple(map(int, s)) for s in ['11121131221', '11121231121']]
    domains = []
    for x, y, z in itertools.product(range(4), repeat=3):
        if x in (1,3) or (y,z) not in [(0,3),(3,0)] or x == y:
            continue
        b = [0,1,0,1,3,x,y,z,1,0,1]
        require(set(range(4)) - {b[i] for i in g[11] if i < n} == {2},
                'The ear is not forced to colour 2')
        require(1 in set(range(4)) - {b[i] for i in g[14] if i < n},
                'The neighbouring interior list lost colour 1')
        w = trace(b)
        require(w in initial + [residual], 'Unexpected guard form')
        domains.append({'segment': [x,y,z], 'boundary': b, 'word': list(w)})
    require(len(domains) == 3, 'Guard cardinality differs')

    checked = {}
    def direct(w):
        w = tuple(w)
        if w in checked:
            return checked[w]
        b = boundary(w)
        assignment, _ = eliminate(g, n, b)
        dfs = complete_patch(g, b)
        require((assignment is None) == (dfs is None), 'Independent extension checks disagree')
        checked[w] = assignment is not None
        if assignment is not None:
            colours = b + [assignment[i] for i in range(n,len(g))]
            require(all(colours[u] != colours[v] for u in range(len(g)) for v in g[u]),
                    'Reconstructed source colouring is improper')
            require(trace(colours[:n]) == w, 'Reconstruction changed the requested trace')
        return checked[w]

    majority_rows = []
    for s, w in enumerate(middle):
        slots = [i for i, c in enumerate(w) if c != 1]
        order = [7,8,9,3,5,6] if s == 0 else [6,8,9,3,4,5]
        require(set(order) == set(slots) and len(slots) == 6, 'Active coordinates differ')
        block = order[:4]
        require(len(slots) < 2*len(block), 'Block is not a majority')
        good = {tuple(sorted(p)) for p in zip(block, block[1:])}
        results = [flip(w,1,[p]) for p in sorted(good)]
        require(all(direct(t) for t in results), 'A majority chord answer cannot extend')
        layouts = pairings(len(slots))
        require(len(layouts) == 5, 'Matching cover differs')
        for m in layouts:
            pairs = {tuple(sorted((slots[a],slots[b]))) for a,b in m}
            require(bool(pairs & good), 'An exterior matching avoids the block')
        majority_rows.append({'word': list(w), 'block': block, 'successful_pairs': sorted(good),
                              'matching_layouts': len(layouts), 'direct_answers': [list(t) for t in results]})

    anchor_rows = []
    def anchor(w, fixed, a, allowed):
        slots = [i for i,c in enumerate(w) if c != fixed]
        require(a in slots, 'Chosen anchor is inactive')
        k = slots.index(a)
        partners = [b for j,b in enumerate(slots) if (j-k) % 2]
        replies = []
        for b in partners:
            t = flip(w, fixed, [(a,b)])
            extends = direct(t)
            require(extends or t in allowed, 'Unaccounted nonterminal anchor reply')
            replies.append({'partner': b, 'word': list(t), 'direct': extends})
        require(partners, 'Empty anchor reply domain')
        anchor_rows.append({'word': list(w), 'fixed': fixed, 'anchor': a, 'replies': replies})

    for s, w in enumerate(initial):
        anchor(w, 3, 9, {middle[s]})
    anchor(extra[0], 1, 3, set())
    anchor(extra[1], 3, 7, {middle[0]})
    anchor(residual, 3, 9, set(extra))
    require(all(not direct(w) for w in initial + middle + [residual] + extra),
            'A purported nonterminal is already direct')
    require(boundary(initial[0])[2] == 0, 'Guard lost its distinguishing boundary colour')
    return {'evidence': 'Kernel-certified symbolic reconstruction and same-exterior repair; independent source replay.',
            'source_sha256': sha256(source).hexdigest(), 'guard_forms': domains,
            'majority_consumers': majority_rows, 'anchor_consumers': anchor_rows,
            'max_chord_moves_in_displayed_strategy': 3,
            'distinct_policy_nodes': 7, 'structural_selection_laws': 2,
            'source_traces_checked': len(checked), 'direct_traces_reconstructed': sum(checked.values()),
            'new_stored_colour_witness_bytes': 0,
            'limits': ['The guard has three normalized boundary forms of one decoded source.',
                       'Finite source-domain and terminal-relation checks remain; the program independently cross-checks five matching layouts.',
                       'This does not establish full-source repair, a strict ambient reduction or geometric supply.',
                       'No catalogue deletion, original-certificate replacement or net whole-proof saving is claimed.'],
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
