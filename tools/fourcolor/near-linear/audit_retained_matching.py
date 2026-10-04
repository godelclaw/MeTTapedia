#!/usr/bin/env python3
"""Replay two source repairs coordinated within one exterior matching.

The Lean proofs use interval exclusion, not the matching enumeration here.
Both terminal branches are checked against the full decoded source graph.
"""
import argparse
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip, interval_possible
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_strip_partial import partial
from generate_exceptional_repair import boundary, pairings


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Source pin differs')
    ring, adj = graph(raw)
    require(ring == 11 and len(adj) == 19, 'Source size differs')
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripCoupledRepair.lean'
    text = lean.read_text()

    def block(name):
        return re.search(rf'^def {name}\b(.*?)(?=^\S)', text, re.M | re.S)[1]

    def pairs(name, side):
        value = re.search(rf'\| {side} => \[([^\]]+)\]', block(name))[1]
        return [tuple(map(int, pair)) for pair in re.findall(r'\((\d+),(\d+)\)', value)]

    def extends(word):
        witness = complete_patch(adj, boundary(word))
        if witness is not None:
            require(all(witness[u] != witness[v] for u, ns in enumerate(adj) for v in ns),
                    'Reconstructed source witness is improper')
        return witness is not None

    results = []
    for side, anchor in [('false', 1), ('true', 2)]:
        word = tuple(map(int, re.findall(r'c([0-3])',
            re.search(rf'\| {side} => !\[([^\]]+)\]', block('source'))[1])))
        require(len(word) == 11 and not extends(word), 'Input is not a nonextension')
        require('if s then 2 else 1' in block('anchor'), 'Anchor definition differs')
        singles = pairs('singlePairs', side)
        doubles = pairs('doublePairs', side)
        slots = [i for i,c in enumerate(word) if c != 3]
        edges = {(a,b) for i,a in enumerate(slots) for j,b in enumerate(slots) if (i-j) % 2}
        require(all(extends(flip(word, 3, [p])) == (tuple(sorted(p)) in singles) for p in edges),
                'Successful single pairs differ from exact extension')
        for p,q in doubles:
            require(len({0,p,anchor,q}) == 4, 'Double branch repeats a component endpoint')
            require(extends(flip(word, 3, [(0,p),(anchor,q)])), 'Double branch does not extend')
        for p,q in product(range(11), repeat=2):
            bad = {(i,j) for i,j in edges if tuple(sorted((i,j))) not in singles and
                   (i != 0 or j == p) and (j != 0 or i == p) and
                   (i != anchor or j == q) and (j != anchor or i == q)}
            require((p,q) in doubles or not interval_possible(slots,bad),
                    'Interval selection leaves an unresolved case')
        single_count, double_count = 0, 0
        used_doubles = set()
        example = None
        for layout in pairings(len(slots)):
            chords = [(slots[a],slots[b]) for a,b in layout]
            if any(p in singles for p in chords):
                single_count += 1
                continue
            mate = dict(chords) | {b:a for a,b in chords}
            chosen = (mate[0],mate[anchor])
            require(chosen in doubles, 'Matching avoids every selected repair')
            selected = [(0,chosen[0]),(anchor,chosen[1])]
            require(not any(extends(flip(word,3,[p])) for p in chords),
                    'Double branch has an unrecorded single repair')
            require(extends(flip(word,3,selected)), 'Coupled repair fails on actual source')
            double_count += 1
            used_doubles.add(chosen)
            if example is None:
                example = {'matching': chords, 'selected_chords': selected,
                           'each_single_chord_fails': True, 'joint_result_extends': True}
        require(used_doubles == set(doubles), 'An unused double branch is stored')
        results.append({'input': ''.join(map(str,word)), 'anchors': [0,anchor],
                        'active_ports': len(slots), 'matchings_program_checked': single_count+double_count,
                        'single_branch_matchings': single_count, 'double_branch_matchings': double_count,
                        'single_pairs': singles, 'double_partner_pairs': doubles,
                        'genuine_joint_example': example})
    require([(r['single_branch_matchings'],r['double_branch_matchings']) for r in results] ==
            [(35,7),(41,1)], 'Consumer census differs')
    # A distinct test of the proposed scalar progress measure. Each colour pair
    # has an adverse matching; these are not asserted to coexist in one exterior.
    hard = tuple(map(int, '12311221133'))
    require(any(partial(adj, ring, boundary(hard), omitted) is not None
                for omitted in combinations(range(8), 2)), 'Hard input needs more than two holes')
    adverse = [[(1,10),(2,9),(5,6)],
               [(0,2),(3,10),(4,7),(8,9)],
               [(0,1),(3,8),(4,5),(6,7)]]
    checked_subsets = 0
    for fixed, chords in enumerate(adverse, 1):
        slots = [i for i,c in enumerate(hard) if c != fixed]
        ranks = {v:i for i,v in enumerate(slots)}
        layout = tuple((ranks[a],ranks[b]) for a,b in chords)
        require(layout in pairings(len(slots)), 'Adverse response is not a noncrossing matching')
        for size in range(len(chords)+1):
            for selected in combinations(chords,size):
                b = boundary(flip(hard,fixed,selected))
                require(all(partial(adj, ring, b, omitted) is None for count in (0,1)
                            for omitted in combinations(range(8),count)),
                        'An adverse response has a strictly improving subset')
                checked_subsets += 1
    obstruction = {'input': ''.join(map(str,hard)), 'initial_minimum_holes':2,
                   'adverse_matchings_by_fixed_colour':adverse,
                   'all_component_subsets_checked':checked_subsets,
                   'each_result_requires_at_least_two_holes':True,
                   'scope':'Program evidence in the abstract matching game. No common physical exterior realizing the three adverse matchings is supplied.'}
    return {'evidence': 'Stable exterior recovery, general two-anchor law and both consumers are Lean proved; explicit matching census is an independent program check.',
            'source_sha256':sha256(raw).hexdigest(),
            'catalogue_revision':'c2ce7a96e35256201526e2abb51a39d04a588b53',
            'attribution':'Yuta Inoue D0099, MIT; Gonthier/Emery chord scan and chromogram semantics.',
            'consumers':results, 'failed_strict_batch_descent':obstruction,
            'kernel_matching_layout_checks':0,
            'new_stored_source_colouring_bytes':0,
            'limits':['Two source inputs, not full D0099 reducibility.',
                      'Matching retention uses one colour pair; it does not establish compatibility between arbitrary different colour-pair matchings.',
                      'The Lean endpoint supplies a source colouring and the same Kempe-closed exterior predicate. No explicit ambient recolouring history or runtime bound is extracted.',
                      'No geometric supply, strict ambient reduction or catalogue deletion is established.'],
            'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent),indent=2)+'\n'
    if args.output:
        args.output.write_text(payload)
    print(payload,end='')
