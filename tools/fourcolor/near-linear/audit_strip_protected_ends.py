#!/usr/bin/env python3
"""Replay the protected end-triangle family on the pinned D0099 source.

The local family is kernel checked separately. The optional matching games
are discovery evidence; their ranks are not exported as proof certificates.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_end_phase import end
from audit_strip_flexibility import code
from audit_strip_partial import partial
from generate_exceptional_repair import boundary, pairings, traces


def safe(segment, fixed):
    return all(end(*[c ^ fixed if cut <= i else c for i,c in enumerate(segment)])
               for cut in range(6))


def family(b, fixed):
    x, y, z = b[9], b[10], b[3]
    return (b[0] == x and b[1] == y and b[2] == x and x != y and x != z and
            fixed != 0 and fixed != x ^ y and (z == y or fixed == x ^ z))


def game(words, left, both, direct):
    indices = {code(tuple(p[c-1] for c in w)): i
               for i,w in enumerate(words) for p in permutations((1,2,3))}
    actions = []
    for w in words:
        phases = []
        for fixed in (1,2,3):
            active = [j for j,c in enumerate(w) if c != fixed]
            require(len(active) % 2 == 0, 'Odd active set')
            rows = []
            for layout in pairings(len(active)):
                outcomes = [code(w)]
                for a,d in layout:
                    mask = (fixed << (2*active[a])) | (fixed << (2*active[d]))
                    outcomes += [o ^ mask for o in outcomes]
                rows.append(frozenset(indices[o] for o in outcomes))
            phases.append(rows)
        actions.append(phases)

    def closure(target, allowed):
        require(all(not target[i] or allowed[i] for i in range(len(words))),
                'Target leaves the invariant')
        ranks = [0 if t else -1 for t in target]
        layers = []
        while True:
            added = [i for i in range(len(words)) if allowed[i] and ranks[i] < 0 and
                     any(all(any(ranks[j] >= 0 for j in row) for row in phase)
                         for phase in actions[i])]
            if not added:
                return {'initial': sum(target), 'layers': layers,
                        'unresolved': sum(allowed[i] and r < 0 for i,r in enumerate(ranks))}
            layers.append(len(added))
            for i in added:
                ranks[i] = len(layers)

    prepare = closure(both, left)
    finish = closure(direct, both)
    require(prepare == {'initial': 4503, 'layers': [1476,309], 'unresolved': 0},
            'Preparation game differs')
    require(finish == {'initial': 1587, 'layers': [705,552,508,471,305,161,114,89,11],
                       'unresolved': 0}, 'Continuation game differs')
    return {'status': 'program evidence only', 'prepare_preserving_left': prepare,
            'complete_preserving_both': finish,
            'scope': 'Choose a palette; every noncrossing matching must admit a batch to an earlier layer. The invariant holds at layer endpoints, not necessarily after each component of a batch. No physical switch bound is proved.'}


def verify(here, run_game=False):
    raw = (here/'D0099.conf').read_bytes()
    digest = sha256(raw).hexdigest()
    require(digest == '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Pinned source differs')
    ring, adj = graph(raw)
    require((ring,len(adj)) == (11,19), 'Source dimensions differ')
    palettes = Counter()
    for segment in product(range(4), repeat=5):
        if any(segment[i] == segment[i+1] for i in range(4)) or not end(*segment):
            continue
        count = sum(safe(segment,f) for f in (1,2,3))
        require(count > 0, 'No safe palette for a proper colourable end')
        palettes[count] += 1
    counts = Counter()
    words = traces(11)
    left, both, direct = [], [], []
    for word in words:
        b = boundary(word)
        left.append(end(*b[4:9]))
        both.append(partial(adj,ring,b,[2,4]) is not None)
        direct.append(partial(adj,ring,b,[]) is not None)
        choices = [f for f in (1,2,3) if family(b,f) and safe(b[4:9],f)]
        if not choices:
            continue
        counts['protected_boundary_classes'] += 1
        require(left[-1] and not both[-1], 'Family input is not a genuine continuation')
        for fixed in choices:
            require(word[9] != fixed, 'Inactive repair anchor')
            for partner in range(11):
                if partner == 9:
                    continue
                lo, hi = sorted((9,partner))
                d = [c ^ fixed if lo < i <= hi else c for i,c in enumerate(b)]
                require(end(*d[4:9]), 'Repair lost the left triangle')
                witness = partial(adj,ring,d,[2,4])
                require(witness is not None, 'Repair did not restore both triangles')
                counts['all_partner_core_checks'] += 1
                if word[partner] != fixed:
                    colouring = dict(enumerate(d)) | witness
                    require(all(colouring[u] != colouring[v] for u in colouring
                                for v in adj[u] if v in colouring),
                            'Actual induced-source colouring has a monochromatic edge')
                    counts['active_partner_source_checks'] += 1
    require(counts['protected_boundary_classes'] == 176 and
            counts['all_partner_core_checks'] == 2080, 'Family census differs')
    result = {'status': 'independent protected-end replay passed', 'source_sha256': digest,
              'proper_boundary_classes': len(words), 'left_colourable': sum(left),
              'both_ends_colourable': sum(both), 'full_extension': sum(direct),
              'proper_left_segments_by_safe_palette_count': dict(palettes),
              'family_checks': dict(counts), 'restored_core_vertices': 6,
              'remaining_bridge_vertices': [2,4],
              'limits': ['Safe-palette intersection is a hypothesis of this family law.',
                         'No full-source repair or geometric supply is established.',
                         'Census and optional game counts are independent program evidence.']}
    if run_game:
        result['matching_games'] = game(words,left,both,direct)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase-game', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent,args.phase_game),indent=2)+'\n'
    if args.output:
        args.output.write_text(payload)
    print(payload,end='')
