#!/usr/bin/env python3
"""Replay the uniform end-triangle phase and optionally its continuation game.

The first phase has a Lean theorem for every proper boundary. The optional
game is discovery evidence: its implicit rank table is not a Lean repair
certificate, a compact second-phase theorem, or a physical switch bound.
"""
import argparse
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_strip_flexibility import code
from audit_two_port_core import eliminate
from generate_exceptional_repair import boundary, pairings, traces


def end(x, y, z, u, v):
    return any(a != d for a in set(range(4)) - {z, u, v}
               for d in set(range(4)) - {x, y, z})


def release(b, partner):
    fixed = b[4] ^ b[6]
    a, d = sorted((4, partner))
    return [c ^ fixed if a < i <= d else c for i, c in enumerate(b)]


def phase_game(adj, words, observations):
    indices = {code(tuple(p[c - 1] for c in w)): i
               for i, w in enumerate(words) for p in permutations((1, 2, 3))}
    direct = []
    for w in words:
        b = boundary(w)
        witness, _ = eliminate(adj, 11, b)
        yes = witness is not None
        require(yes == (complete_patch(adj, b) is not None), 'Extension solvers disagree')
        direct.append(yes)
    actions, layouts = [], 0
    for i, w in enumerate(words):
        palettes = []
        if not direct[i]:
            for fixed in (1, 2, 3):
                slots = [j for j, c in enumerate(w) if c != fixed]
                require(len(slots) % 2 == 0, 'Odd active boundary')
                rows = []
                for layout in pairings(len(slots)):
                    outcomes = [code(w)]
                    for a, d in layout:
                        mask = (fixed << (2 * slots[a])) | (fixed << (2 * slots[d]))
                        outcomes += [o ^ mask for o in outcomes]
                    rows.append(frozenset(indices[o] for o in outcomes))
                    layouts += 1
                palettes.append(rows)
        actions.append(palettes)

    def accepts(i, good):
        return any(all(any(good(j) for j in row) for row in rows) for rows in actions[i])

    def closure(allowed):
        rank = [0 if yes else -1 for yes in direct]
        layers = []
        while True:
            new = [i for i in range(len(words)) if allowed(i) and rank[i] < 0 and
                   accepts(i, lambda j: rank[j] >= 0)]
            if not new:
                return rank, layers
            layers.append(len(new))
            for i in new:
                rank[i] = len(layers)

    full_rank, full_layers = closure(lambda _: True)
    left_rank, left_layers = closure(lambda i: observations[i][0])
    hardest = [i for i, r in enumerate(full_rank) if r == len(full_layers)]
    release_counts = {
        'left': sum(accepts(i, lambda j: observations[j][0]) for i in hardest),
        'right': sum(accepts(i, lambda j: observations[j][1]) for i in hardest),
        'both': sum(accepts(i, lambda j: all(observations[j])) for i in hardest)}
    return {
        'status': 'program evidence; no Lean second-phase theorem',
        'noncrossing_layouts': layouts,
        'direct_extensions': sum(direct),
        'unrestricted_layers': full_layers,
        'unrestricted_unresolved': full_rank.count(-1),
        'left_feasible_classes': sum(a for a, _ in observations),
        'left_preserving_layers': left_layers,
        'left_preserving_unresolved': sum(r < 0 and observations[i][0]
                                         for i, r in enumerate(left_rank)),
        'last_unrestricted_layer_classes': len(hardest),
        'last_layer_one_batch_release': release_counts,
        'scope': 'Existential palette, universal noncrossing matching, existential batch to an earlier layer. The restricted game keeps the left triangle feasible at every stage. Separate triangle feasibility does not imply a whole-core colouring.'}


def verify(here, game=False):
    raw = (here / 'D0099.conf').read_bytes()
    digest = sha256(raw).hexdigest()
    require(digest == '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Pinned D0099 source changed')
    ring, adj = graph(raw)
    require((ring, len(adj)) == (11, 19), 'Wrong source dimensions')
    words = traces(11)
    observations, bad, updates = [], 0, 0
    for w in words:
        b = boundary(w)
        lists = [set(range(4)) - {b[j] for j in adj[v] if j < 11}
                 for v in range(11, 19)]
        left = any(len(set(c)) == 3 for c in product(*(lists[j] for j in (0, 1, 3))))
        right = any(len(set(c)) == 3 for c in product(*(lists[j] for j in (5, 6, 7))))
        require(left == end(*b[4:9]), 'Local relation differs from the decoded triangle')
        observations.append((left, right))
        if left:
            continue
        bad += 1
        fixed = b[4] ^ b[6]
        require(fixed != 0 and w[4] != fixed, 'Anchor is not active')
        for partner in range(11):
            if partner == 4:
                continue
            require(end(*release(b, partner)[4:9]), 'Anchored end release failed')
            updates += 1
    local_bad, local_updates = 0, 0
    for segment in product(range(4), repeat=5):
        if end(*segment):
            continue
        local_bad += 1
        b = [0] * 4 + list(segment) + [0, 0]
        for partner in (0, 5, 6, 7, 8, 10):
            require(end(*release(b, partner)[4:9]), 'Local partner region failed')
            local_updates += 1
    report = {
        'status': 'independent first-phase replay passed', 'source': 'D0099.conf',
        'source_sha256': digest, 'proper_boundary_classes': len(words),
        'initial_left_failures': bad, 'distinct_partner_updates': updates,
        'five_port_assignments': 4 ** 5, 'obstructed_five_port_assignments': local_bad,
        'local_partner_region_checks': local_updates,
        'stored_boundary_words': 0, 'stored_core_colourings': 0,
        'limits': ['Only the left triangle is restored by the Lean first-phase law.',
                   'No new full-source reduction or geometric coverage follows.']}
    if game:
        report['continuation_game'] = phase_game(adj, words, observations)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase-game', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent, args.phase_game)
    payload = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
