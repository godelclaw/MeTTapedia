#!/usr/bin/env python3
"""Bounded discovery test of catalogue strips around flat seven-triangles.

Samples are related spherical triangulations, not independent random maps.
Success is only discovery evidence. No general coverage, reducibility, or
minimal-counterexample claim follows from a successful finite sample.
"""

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import random

from audit_closing_triangle_strips import catalogue_inventory
from audit_chain_boundary import distances, subdivide
from audit_seven_pair_example import source_rule, tested_cores
from probe_flat_pairs import geometry, initial_faces, read_rules, reading


def probe(here, catalogue, fixture, names, samples):
    pool = [(name, *source_rule(catalogue, name))
            for name in fixture['other_configurations'] + names]
    rules, _ = read_rules(here)
    counts, hits = Counter(), Counter()
    for seed in range(30):
        rng = random.Random(902170 + seed)
        faces = subdivide(initial_faces())
        history = []
        for step in range(1, 601):
            darts, ns, _, _ = geometry(faces)
            allowed = [(a, b, c, d) for (a, b), (_, c) in darts.items() if a < b
                       for _, d in [darts[b, a]] if min(len(ns[a]), len(ns[b])) >= 6
                       and max(len(ns[c]), len(ns[d])) <= 6 and d not in ns[c]]
            if not allowed:
                break
            a, b, c, d = rng.choice(allowed)
            i, _ = darts[a, b]
            j, _ = darts[b, a]
            faces[i], faces[j] = (c, d, b), (d, c, a)
            history.append([a, b, c, d])
            if step % 10:
                continue
            darts, ns, nxt, prev = geometry(faces)
            counts['spheres'] += 1
            charges = {}
            for u in ns:
                if len(ns[u]) != 7:
                    continue
                total = -10
                for v in ns[u]:
                    for a, b, sign in ((v, u, 1), (u, v, -1)):
                        total += sum(sign * r[1][0][3] for r in rules
                                     if reading(r, a, b, ns, nxt, prev) is not None)
                charges[u] = total
            for triangle in faces:
                if not all(charges.get(v) == 0 for v in triangle):
                    continue
                counts['flat_triangles'] += 1
                ds = [distances(ns, v) for v in triangle]
                ball = {v for v in ns if min(d[v] for d in ds) <= 2}
                if any(core <= ball for _, core in tested_cores(ns, nxt, prev)):
                    counts['simple_covered'] += 1
                    continue
                found = None
                for name, rule, rows in pool:
                    n, ring = rows[0]
                    root_degree = rule[1][rule[1][0][1]][1]
                    for a in sorted(ball):
                        if len(ns[a]) != root_degree:
                            continue
                        for b in sorted(ns[a] & ball):
                            for fw, bw in ((nxt, prev), (prev, nxt)):
                                images = reading(rule, a, b, ns, fw, bw)
                                counts['source_tests'] += 1
                                if images is None or len(set(images)) != n or not set(images[ring:]) <= ball:
                                    continue
                                if not all(ns[images[i - 1]] == {images[v - 1] for v in vs}
                                           for i, _, *vs in rows[1:]):
                                    continue
                                found = name
                                break
                            if found:
                                break
                        if found:
                            break
                    if found:
                        break
                if found:
                    counts['source_covered'] += 1
                    hits[found] += 1
                else:
                    return {'counts': dict(counts), 'hits': dict(hits),
                            'unclassified': {'centres': triangle, 'edge_flip_history': history,
                                             'short_cycle_obstruction_not_yet_checked': True}}
            if counts['spheres'] >= samples:
                return {'counts': dict(counts), 'hits': dict(hits), 'unclassified': None}
    return {'counts': dict(counts), 'hits': dict(hits), 'unclassified': None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalogue', type=Path, required=True)
    parser.add_argument('--samples', type=int, default=1791, choices=range(1, 1801),
                        metavar='1..1800')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    fixture = json.loads((here / 'closing-triangle-strip-example.json').read_text())
    _, _, names, _ = catalogue_inventory(args.catalogue, fixture)
    result = probe(here, args.catalogue, fixture, names, args.samples)
    result.update({'evidence': 'Bounded discovery only; no exhaustive coverage claim.',
                   'seed_base': 902170, 'maximum_seeds': 30, 'flips_per_seed': 600,
                   'sample_every': 10, 'requested_samples': args.samples,
                   'catalogue_strips': len(names), 'catalogue_revision': fixture['catalogue']['revision'],
                   'program_sha256': sha256(Path(__file__).read_bytes()).hexdigest()})
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
