#!/usr/bin/env python3
"""Replay local triangle support against exact colouring of the pinned D0099.

The census is independent program evidence, not a kernel classification.
Lean separately proves the surviving counterexample and exact composition.
No global repair strategy or boundary table is exported.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path

from audit_diamond_sources import require
from audit_adaptive_chords import flip
from audit_five_triangle_collapse import graph
from audit_strip_partial import partial
from generate_exceptional_repair import boundary, pairings, traces


def support(domains, triangles):
    """Remove colours without a compatible assignment on an incident triangle."""
    result = [set(d) for d in domains]
    rounds = 0
    while True:
        before = [frozenset(d) for d in result]
        for triangle in triangles:
            rows = [cs for cs in product(*(result[v] for v in triangle))
                    if len(set(cs)) == 3]
            for i, v in enumerate(triangle):
                result[v].intersection_update(cs[i] for cs in rows)
        rounds += 1
        if not all(result) or before == [frozenset(d) for d in result]:
            return result, rounds


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    digest = sha256(raw).hexdigest()
    require(digest == '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Pinned source differs')
    ring, adj = graph(raw)
    require((ring, len(adj)) == (11, 19), 'Source dimensions differ')
    core = [{u-ring for u in adj[ring+v] if u >= ring} for v in range(8)]
    triangles = [t for t in combinations(range(8), 3)
                 if all(v in core[u] for u, v in combinations(t, 2))]
    require(triangles == [(0,1,3),(1,2,3),(1,2,4),(2,4,6),(2,5,6),(5,6,7)],
            'Core triangles differ')
    counts, survivors, maximum = Counter(), [], 0
    for word in traces(ring):
        b = boundary(word)
        domains = [set(range(4)) - {b[u] for u in adj[ring+v] if u < ring}
                   for v in range(8)]
        retained, rounds = support(domains, triangles)
        maximum = max(maximum, rounds)
        witness = partial(adj, ring, b, [])
        if witness is not None:
            require(all(retained), 'Triangle filtering rejected an actual colouring')
            require(all(witness[ring+v] in retained[v] for v in range(8)),
                    'Triangle filtering discarded a witness colour')
            counts['extends'] += 1
        elif not all(retained):
            counts['rejected_by_triangle_support'] += 1
        else:
            counts['nonextending_fixed_points'] += 1
            survivors.append({'edgeword': ''.join(map(str, word)), 'boundary': b,
                              'domains': list(map(sorted, retained))})
    require(dict(counts) == {'extends': 1587, 'rejected_by_triangle_support': 5793,
                            'nonextending_fixed_points': 1}, 'Census differs')
    require(survivors == [{'edgeword': '12212233312',
                          'boundary': [0,1,3,1,0,2,0,3,0,3,2],
                          'domains': [[1,2],[1,2,3],[2,3],[1,3],[1,2],[0,2],[0,1],[3]]}],
            'Counterexample differs')
    example = survivors[0]
    b = example['boundary']
    left, right = [], []
    for a, c in product(range(4), repeat=2):
        for live, result in [((0,1,2,3,4), left), ((2,4,5,6,7), right)]:
            lists = [set(range(4)) - {b[u] for u in adj[ring+v] if u < ring}
                     for v in live]
            lists[live.index(2)] &= {a}
            lists[live.index(4)] &= {c}
            if any(all(cs[live.index(u)] != cs[live.index(v)]
                       for u, v in combinations(live, 2) if v in core[u])
                   for cs in product(*lists)):
                result.append((a,c))
    require(left and right and all(a == 2 for a,c in left) and
            all(a == 3 for a,c in right), 'Shared-vertex conflict differs')
    word = tuple(map(int, example['edgeword']))
    exchanges = [(6,7),(7,8),(8,10),(7,4)]
    for exchange in exchanges:
        require(partial(adj, ring, boundary(flip(word, 1, [exchange])), []) is not None,
                'Repair exchange does not extend')
    active = [i for i,c in enumerate(word) if c != 1]
    successes = {tuple(sorted(p)) for p in exchanges}
    matchings = pairings(len(active))
    for matching in matchings:
        require(any(tuple(sorted((active[i],active[j]))) in successes
                    for i,j in matching), 'Matching has no certified exchange')
    return {'status': 'independent triangle-support census passed',
            'source_sha256': digest, 'proper_boundary_classes': sum(counts.values()),
            'program_only_counts': dict(counts), 'maximum_filter_sweeps': maximum,
            'kernel_counterexample': example, 'left_interface': left, 'right_interface': right,
            'positive_control': {'successful_exchanges': exchanges,
                                 'noncrossing_matchings': len(matchings),
                                 'single_exchange_per_matching': True},
            'limits': ['The census is not a Lean classification theorem.',
                       'Failure fixes the boundary; Kempe repair is not refuted.',
                       'Compatible full-source repair is proved for this one boundary only.',
                       'No universal source repair, strict reduction or geometric coverage is claimed.']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
