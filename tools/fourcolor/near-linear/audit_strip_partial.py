#!/usr/bin/env python3
"""Replay the sharp partial-colouring bound and test strict defect descent.

Lean proves the arbitrary-boundary construction, sharpness, exact coupled
restoration and connected fixed-boundary fibres. The complete defect census
and Kempe progress tests below are independent program evidence only.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

from audit_adaptive_chords import interval_possible
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_majority_repair import policies
from generate_exceptional_repair import boundary, traces

HOLES = {0, 2, 5}


def partial(g, ring, b, omitted):
    active = set(range(ring, len(g))) - {ring + v for v in omitted}
    lists = {v: set(range(4)) - {b[j] for j in g[v] if j < ring} for v in active}

    def search(left, colours):
        if not left:
            return dict(colours)
        allowed = {v: lists[v] - {colours[j] for j in g[v] if j in colours} for v in left}
        v = min(left, key=lambda x: len(allowed[x]))
        for c in sorted(allowed[v]):
            colours[v] = c
            found = search(left - {v}, colours)
            if found is not None:
                return found
        colours.pop(v, None)
        return None

    return search(active, {})


def spine(b):
    avoid = lambda a, c, d: min(set(range(4)) - {a, c, d})
    f = {7: avoid(b[0], b[1], b[10]), 3: avoid(b[4], b[5], b[6])}
    f[6] = avoid(b[9], b[10], f[7])
    f[4] = avoid(b[8], b[9], f[6])
    f[1] = avoid(b[8], f[3], f[4])
    return f


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Source pin differs')
    ring, g = graph(raw)
    require(ring == 11 and len(g) == 19, 'Source domain differs')
    live = set(range(8)) - HOLES
    kept_edges = {(u, v) for u in live for v in live if u < v and ring+v in g[ring+u]}
    require(kept_edges == {(1,3), (1,4), (4,6), (6,7)}, 'Retained core is not the path')
    words = traces(ring)
    hole_counts = []
    for w in words:
        b = boundary(w)
        f = spine(b)
        colour = dict(enumerate(b)) | {ring+v: c for v,c in f.items()}
        require(all(colour[u] != colour[v] for u in colour for v in g[u] if v in colour),
                'Greedy spine violates a retained source edge')
        minimum = next((k for k in range(3) if any(partial(g, ring, b, hs) is not None
                       for hs in combinations(range(8), k))), 3)
        hole_counts.append(minimum)
    counts = dict(sorted(Counter(hole_counts).items()))
    require(counts == {0:1587, 1:4289, 2:1441, 3:64}, 'Partial-colouring census differs')

    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripPartialColouring.lean'
    source = lean.read_text().split('def testBoundary', 1)[1].split('theorem example_proper', 1)[0]
    b = list(map(int, re.findall(r'c([0-3])', source)))
    require(b == boundary(tuple(map(int, '11211231112'))), 'Sharpness boundary differs')
    lists = [sorted(set(range(4)) - {b[j] for j in g[ring+v] if j < ring}) for v in range(8)]
    require(lists[0] == lists[3] == [1] and lists[5] == lists[7] == [3] and
            lists[2] == lists[4] == lists[6] == [0,1], 'Disjoint obstructions differ')
    require(all(partial(g, ring, b, hs) is None for k in range(3)
                for hs in combinations(range(8), k)), 'Two-hole lower bound failed')

    index, cache = policies(words)

    def improves(i, known):
        return any(not interval_possible(slots, {p for p,j in pairs.items() if j not in known})
                   for slots, pairs, _, _ in cache[i])

    progress = []
    for k in (1,2,3):
        domain = {i for i,h in enumerate(hole_counts) if h == k}
        smaller = {i for i,h in enumerate(hole_counts) if h < k}
        once = smaller | {i for i in range(len(words)) if improves(i, smaller)}
        twice = once | {i for i in domain if improves(i, once)}
        progress.append({'holes': k, 'inputs': len(domain),
                         'one_adaptive_step_improves': len(domain & once),
                         'two_adaptive_steps_improve': len(domain & twice),
                         'first_two_step_failure': next((''.join(map(str,words[i]))
                             for i in sorted(domain - twice)), None)})
    require([r['one_adaptive_step_improves'] for r in progress] == [525,1251,64],
            'One-step descent census differs')
    require([r['two_adaptive_steps_improve'] for r in progress] == [917,1437,64],
            'Two-step descent census differs')
    return {'evidence': 'Sharp bound, reconstruction and fixed-boundary fibre theorem are Lean proved; census and progress tests are program evidence.',
            'source_sha256': sha256(raw).hexdigest(),
            'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
            'attribution': 'Yuta Inoue D0099 catalogue, MIT; source semantics from Gonthier/Emery.',
            'canonical_inputs': len(words), 'fixed_omitted_core_vertices': sorted(HOLES),
            'retained_core_path': [3,1,4,6,7], 'minimum_hole_census': counts,
            'sharpness': {'input': '11211231112', 'boundary': b, 'core_lists': lists,
                'disjoint_uncolourable_pieces': [[0,3],[2,4,6],[5,7]],
                'all_omission_sets_of_size_at_most_two_rejected': True},
            'strict_defect_descent': progress,
            'new_stored_colour_witness_bytes': 0,
            'limits': ['Minimum-hole counts and failed progress tests concern the specified fixed source.',
                       'The abstract adverse matchings need not be simultaneously realized by one physical exterior.',
                       'Three-hole restoration and external repair remain open; fixed-boundary fibre connectivity does not imply completion.',
                       'No geometric supply, strict ambient reduction or catalogue deletion is established.'],
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
