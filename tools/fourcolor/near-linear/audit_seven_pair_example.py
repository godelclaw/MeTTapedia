#!/usr/bin/env python3
"""Replay a flat seven-pair fixture and its two four-triangle occurrences.

These are independent program checks. The Lean theorem proves core geometry
for arbitrary readings; it does not kernel-certify this entire sphere.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

from audit_chain_boundary import distances, short_cycles, subdivide
from audit_diamond_sources import read_rows, require
from audit_four_triangle_sources import verify as verify_sources
from generate_rule_traces import compile_traces
from probe_flat_pairs import geometry, initial_faces, read_rules, reading, breadth_first_reading


def tested_cores(ns, nxt, prev):
    for a, vs in ns.items():
        degrees = [len(ns[b]) for b in vs]
        if len(vs) == 7 and set(degrees) <= {5, 6} and degrees.count(5) in (1, 2):
            yield 'one/two-five wheel', {a, *vs}
        for b in vs:
            tips = [nxt[a, b], prev[a, b]]
            if len(vs) == 5 and len(ns[b]) in (5, 6) and all(len(ns[t]) == 5 for t in tips):
                yield 'diamond', {a, b, *tips}
            if len(vs) == 6:
                for turns in (nxt, prev):
                    word = [b]
                    for _ in range(3):
                        word.append(turns[a, word[-1]])
                    if [len(ns[t]) for t in word] in ([5, 6, 5, 5], [5, 6, 6, 5]):
                        yield 'chain', {a, *word}


def source_rule(here, name):
    rows = read_rows((here / name).read_text())
    n, ring = rows[0]
    core = {a: (degree, vs) for a, degree, *vs in rows[1:]}
    adj = {a: set() for a in range(1, n + 1)}
    for a, (_, vs) in core.items():
        for b in vs:
            adj[a].add(b)
            adj[b].add(a)
    for a in range(1, ring + 1):
        b = a % ring + 1
        adj[a].add(b)
        adj[b].add(a)
    sender = min(core)
    receiver = min(adj[sender] & core.keys())
    data = [[n, sender, receiver, 0]]
    for a in range(1, n + 1):
        if a in core:
            degree, vs = core[a]
            data.append([a, degree, degree, *vs])
        else:
            data.append([a, 0, 0, *[x for b in sorted(adj[a]) for x in (b, -1)]])
    return (name, data, compile_traces(data)), rows


def verify(here):
    source_report = verify_sources(here)
    fixture_path = here / 'seven-pair-four-triangle-example.json'
    fixture = json.loads(fixture_path.read_text())
    require(fixture['configuration_revision'] == source_report['revision'], 'Catalogue revision differs')
    faces = subdivide(initial_faces())
    require(faces == list(map(tuple, fixture['initial_faces'])), 'Initial sphere differs')
    for a, b, c, d in fixture['edge_flip_history']:
        darts, ns, _, _ = geometry(faces)
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d) and d not in ns[c], 'Illegal edge flip')
        require(min(len(ns[a]), len(ns[b])) >= 6 and max(len(ns[c]), len(ns[d])) <= 6,
                'Flip degree guard differs')
        faces[i], faces[j] = (c, d, b), (d, c, a)
    require(faces == list(map(tuple, fixture['faces'])), 'Final sphere differs')
    darts, ns, nxt, prev = geometry(faces)
    require(len(ns) == fixture['vertices'] == 162, 'Sphere size differs')
    require(len(fixture['edge_flip_history']) == fixture['step'] == 1625, 'Flip count differs')
    require({str(d): n for d, n in Counter(map(len, ns.values())).items()} == fixture['degree_counts'],
            'Degree counts differ')
    require(all(5 <= len(vs) <= 7 for vs in ns.values()), 'Ambient degree bounds fail')
    centres = fixture['centres']
    u, v = centres
    require(centres == [39, 90] and len(ns[u]) == len(ns[v]) == 7, 'Centres differ')
    require({w for w in ns[u] if len(ns[w]) >= 7} == {v}, 'High neighbour is not unique')
    rules, revision = read_rules(here)
    require(revision == fixture['rule_revision'], 'Rule revision differs')
    tests, profiles = 0, []
    for orientation, turns, back in [('source', nxt, prev), ('reverse', prev, nxt)]:
        for centre in centres:
            charge = -10
            transfers = []
            for w in ns[centre]:
                for a, b, sign in ((w, centre, 1), (centre, w, -1)):
                    for rule in rules:
                        one = reading(rule, a, b, ns, turns, back)
                        two = breadth_first_reading(rule[1], a, b, ns, turns, back)
                        require(one == two, 'Rule matchers disagree')
                        tests += 1
                        if one is not None:
                            amount = sign * rule[1][0][3]
                            charge += amount
                            transfers.append([rule[0], a, b, amount])
            require(charge == 0, 'Centre is not flat')
            profiles.append(dict(orientation=orientation, centre=centre, charge=charge, transfers=transfers))
    distance = [distances(ns, c) for c in centres]
    joint = {a for a in ns if min(d[a] for d in distance) <= 3}
    for name, vertices in tested_cores(ns, nxt, prev):
        require(not vertices <= joint, f'{name} core inside the tested radius')
    occurrences = []
    for hit in fixture['source_occurrences']:
        require(sha256((here / hit['name']).read_bytes()).hexdigest() == hit['sha256'], 'Source hash differs')
        rule, rows = source_rule(here, hit['name'])
        images = hit['images']
        n, ring = rows[0]
        require(len(set(images)) == n, 'Occurrence is not injective')
        turns, back = (nxt, prev) if hit['orientation'] == 'source' else (prev, nxt)
        a, b = [images[i - 1] for i in rule[1][0][1:3]]
        require(reading(rule, a, b, ns, turns, back) == images, 'Compiled occurrence differs')
        require(breadth_first_reading(rule[1], a, b, ns, turns, back) == images,
                'Independent occurrence differs')
        core_rows = {a: set(vs) for a, _, *vs in rows[1:]}
        for a, degree, *vs in rows[1:]:
            require(len(ns[images[a - 1]]) == degree and {images[w - 1] for w in vs} == ns[images[a - 1]],
                    'Complete core star differs')
            for b in core_rows:
                require((images[b - 1] in ns[images[a - 1]]) == (b in core_rows[a]), 'Extra core edge')
        occurrences.append(dict(configuration=hit['name'], core_vertices=images[ring:],
            core_radius=max(min(d[w] for d in distance) for w in images[ring:]),
            complete_radius=max(min(d[w] for d in distance) for w in images)))
    return dict(evidence='Independent exact program replay; no universal coverage or new repair claim.',
        vertices=len(ns), flips=fixture['step'], independent_rule_tests=tests,
        short_cycles_checked=short_cycles(faces, darts, ns), obstructing_short_cycles=0,
        tested_core_radius=3, tested_core_occurrences=0, profiles=profiles, occurrences=occurrences,
        fixture_sha256=sha256(fixture_path.read_bytes()).hexdigest(),
        verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'profiles'}, indent=2))


if __name__ == '__main__':
    main()
