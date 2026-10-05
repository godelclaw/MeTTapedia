#!/usr/bin/env python3
"""Replay the local diamond continuation on the pinned D0099 source.

This is independent program evidence accompanying the Lean theorem. It
stores no boundary or matching table and makes no full-core repair claim.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_end_phase import end
from generate_exceptional_repair import boundary, traces


def diamond(t):
    x, y, z, u, v, w = t
    return any(a != d and a != e and d != e and d != c and e != c
               for a, d, e, c in product(set(range(4)) - {u, v, w},
                                         set(range(4)) - {y, z, u},
                                         set(range(4)) - {w},
                                         set(range(4)) - {x, y}))


def normalize(t):
    names = {}
    return tuple(names.setdefault(c, len(names)) for c in t)


def update(b, partner):
    anchor = 4 if b[8] == b[3] else 3
    fixed = b[anchor] ^ b[6]
    lo, hi = sorted((anchor, partner))
    return [c ^ fixed if lo < i <= hi else c for i, c in enumerate(b)]


def partial_extension(adj, b):
    vertices = (11, 12, 13, 14)
    lists = [set(range(4)) - {b[i] for i in adj[v] if i < 11} for v in vertices]
    return any(all(cs[i] != cs[j] for i in range(4) for j in range(i)
                   if vertices[j] in adj[vertices[i]]) for cs in product(*lists))


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    digest = sha256(raw).hexdigest()
    require(digest == '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Pinned source changed')
    ring, adj = graph(raw)
    require((ring, len(adj)) == (11, 19), 'Wrong source dimensions')
    patterns = {(0, 1, 0, 2, 3, 1), (0, 1, 0, 2, 3, 0), (0, 1, 2, 0, 2, 0)}
    local_failures, local_updates = 0, 0
    for t in product(range(4), repeat=6):
        if any(t[i] == t[i+1] for i in range(5)):
            continue
        if not end(*t[1:]) or diamond(t):
            continue
        require(normalize(t) in patterns, 'Unclassified local failure')
        local_failures += 1
        b = [0, 0, 0] + list(t) + [0, 0]
        anchor = 4 if b[8] == b[3] else 3
        fixed = b[anchor] ^ b[6]
        require(fixed != 0 and b[anchor] ^ b[anchor+1] != fixed, 'Inactive anchor')
        for j in range(11):
            if j != anchor:
                require(diamond(update(b, j)[3:9]), 'Local release failed')
                local_updates += 1
    census = Counter()
    words = traces(11)
    for word in words:
        b = boundary(word)
        yes = diamond(b[3:9])
        require(yes == partial_extension(adj, b), 'Local predicate differs from actual source')
        if end(*b[4:9]) and not yes:
            census[str(normalize(b[3:9]))] += 1
            anchor = 4 if b[8] == b[3] else 3
            for j in range(11):
                if j != anchor:
                    require(partial_extension(adj, update(b, j)), 'Source restoration failed')
    return {'status': 'independent diamond continuation replay passed',
            'source_sha256': digest, 'proper_boundary_classes': len(words),
            'left_ready_diamond_blocked': sum(census.values()),
            'local_pattern_counts': dict(census),
            'local_assignments': 4**6, 'local_failed_assignments': local_failures,
            'local_partner_checks': local_updates,
            'whole_boundary_partner_checks': 10 * sum(census.values()),
            'stored_boundary_words': 0, 'stored_matchings': 0,
            'restored_core_vertices': 4, 'remaining_core_vertices': 4,
            'limits': ['Partial source repair only; no complete reduction or coverage claim.']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    payload = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
