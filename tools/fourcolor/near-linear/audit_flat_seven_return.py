#!/usr/bin/env python3
"""Check a closed triangle of flat seven-centres in a spherical triangulation.

This is independent program evidence, not a Lean theorem. It tests a specific
continuation claim and a specified reduction vocabulary. It does not refute
coverage using other reductions or hypotheses on an entire flat ball.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_chain_boundary import distances, short_cycles, subdivide
from audit_diamond_sources import require, validate, read_rows
from audit_seven_pair_example import source_rule, tested_cores
from probe_flat_pairs import (
    geometry, initial_faces, read_rules, reading, breadth_first_reading,
)


def verify_core_map(here):
    """Check the supplied core map, without searching for an isomorphism."""
    path = here / 'flat-seven-return-core-map.json'
    data = json.loads(path.read_text())
    rows = []
    hashes = {}
    for role, fixture_name in [('source', 'flat-seven-return-example.json'),
                               ('target', 'flat-seven-return-extension-example.json')]:
        fixture = json.loads((here / fixture_name).read_text())
        require(data[role] == fixture['source_occurrence']['configuration'],
                'Core comparison does not use the two observed configurations')
        raw = (here / data[role]).read_bytes()
        hashes[data[role]] = sha256(raw).hexdigest()
        require(hashes[data[role]] == fixture['configuration_source']['sha256'],
                'Core comparison source hash differs')
        decoded = read_rows(raw.decode())
        validate(decoded)
        rows.append(decoded)
    source, target = [{a: (degree, vs) for a, degree, *vs in r[1:]} for r in rows]
    mapping = {int(a): b for a, b in data['map'].items()}
    require(set(mapping) == set(source) and set(mapping.values()) == set(target) and
            len(set(mapping.values())) == len(mapping), 'Core map is not a bijection')
    require(type(data['reversed']) is bool, 'Invalid reflection flag')
    degree_table = []
    edge_count = 0
    for a, (degree, vs) in sorted(source.items()):
        b = mapping[a]
        degree2, ws = target[b]
        left = [mapping[v] for v in vs if v in source]
        right = [w for w in ws if w in target]
        require(set(left) == set(right), 'Core adjacency differs')
        if data['reversed']:
            left.reverse()
        require(any(left == right[i:] + right[:i] for i in range(len(right))),
                'Internal cyclic order differs')
        edge_count += len(left)
        degree_table.append({'source': a, 'target': b, 'source_degree': degree,
                             'target_degree': degree2})
    require(degree_table == data['prescribed_degrees'], 'Prescribed-degree table differs')

    def turns(core):
        return {(a, v, vs[(i + 1) % len(vs)])
                for a, (_, vs) in core.items() for i, v in enumerate(vs)
                if v in core and vs[(i + 1) % len(vs)] in core}

    mapped = {(mapping[a], mapping[v], mapping[w]) for a, v, w in turns(source)}
    if data['reversed']:
        mapped = {(a, w, v) for a, v, w in mapped}
    require(mapped == turns(target), 'Internal facial triangles differ')
    require(len(mapped) % 3 == 0 and edge_count % 2 == 0, 'Incomplete core incidence')
    return {'source': data['source'], 'target': data['target'], 'source_sha256': hashes,
            'core_vertices': len(source), 'core_edges': edge_count // 2,
            'core_facial_triangles': len(mapped) // 3, 'global_reflection': data['reversed'],
            'prescribed_degree_changes': sum(r['source_degree'] != r['target_degree']
                                           for r in degree_table),
            'ordered_boundary_ports': [r[0][1] for r in rows],
            'boundary_map_or_repair_transfer_claimed': False,
            'map_sha256': sha256(path.read_bytes()).hexdigest()}


def verify(here, fixture_name='flat-seven-return-example.json'):
    fixture_path = here / fixture_name
    fixture = json.loads(fixture_path.read_text())
    original_path = here / fixture['source_fixture']
    require(sha256(original_path.read_bytes()).hexdigest() == fixture['source_fixture_sha256'],
            'Sphere history source changed')
    original = json.loads(original_path.read_text())
    faces = subdivide(initial_faces())
    require(faces == list(map(tuple, original['initial_faces'])), 'Initial sphere differs')
    prefix = fixture['edge_flip_prefix']
    require(0 <= prefix <= len(original['edge_flip_history']), 'Invalid prefix')
    for a, b, c, d in original['edge_flip_history'][:prefix]:
        darts, ns, _, _ = geometry(faces)
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d) and d not in ns[c], 'Illegal edge flip')
        require(min(len(ns[a]), len(ns[b])) >= 6 and max(len(ns[c]), len(ns[d])) <= 6,
                'Flip violates degree bounds')
        faces[i], faces[j] = (c, d, b), (d, c, a)

    darts, ns, nxt, prev = geometry(faces)
    require(all((v, u) in darts for u, v in darts), 'Surface has an open edge')
    require(len(distances(ns, 0)) == len(ns), 'Surface is disconnected')
    require(all(5 <= len(vs) <= 7 for vs in ns.values()), 'Ambient degree bounds fail')
    centres = fixture['centres']
    require(len(centres) == len(set(centres)) == 3, 'Centres are not distinct')
    require(any(set(f) == set(centres) for f in faces), 'The return is not a facial triangle')
    require(all(len(ns[v]) == 7 for v in centres), 'A centre has the wrong degree')
    cycle_checks = short_cycles(faces, darts, ns)
    distance = [distances(ns, c) for c in centres]
    ball = {v for v in ns if min(d[v] for d in distance) <= 2}
    rules, revision = read_rules(here)
    require(revision == fixture['rule_revision'], 'Rule source revision differs')

    tests, charges, transfers = 0, [], []
    for centre in centres:
        total, matches = -10, []
        for other in sorted(ns[centre]):
            for a, b, sign in ((other, centre, 1), (centre, other, -1)):
                for rule in rules:
                    one = reading(rule, a, b, ns, nxt, prev)
                    two = breadth_first_reading(rule[1], a, b, ns, nxt, prev)
                    require(one == two, 'Independent rule matchers disagree')
                    tests += 1
                    if one is not None:
                        amount = sign * rule[1][0][3]
                        total += amount
                        matches.append([rule[0], a, b, amount])
        require(total == 0, 'A centre is not flat')
        charges.append(total)
        transfers.append({'centre': centre, 'signed_rule_applications': matches})

    # A specific vocabulary, not every reduction formalized in the repository.
    core_hits = [(name, sorted(vs)) for name, vs in tested_cores(ns, nxt, prev) if vs <= ball]
    require(not core_hits, 'A tested simple core occurs in the radius-two union')
    pins = fixture['tested_configuration_sources']
    baseline = {'D0000.conf', 'D0001.conf', 'D0004.conf', 'D0006.conf',
                'D0051.conf', 'D0052.conf', 'D3009.conf'}
    require(set(pins) in (baseline, baseline | {'D0092.conf', 'D0142.conf'}),
            'Unexpected tested vocabulary')
    names = sorted(pins)
    for name in names:
        raw = (here / name).read_bytes()
        require(sha256(raw).hexdigest() == pins[name], f'Source changed: {name}')
    source_hashes = {name: sha256((here / name).read_bytes()).hexdigest() for name in names}
    source_tests = 0
    for name in names:
        rule, rows = source_rule(here, name)
        ring = rows[0][1]
        for a, b in sorted(darts):
            for forward, backward in [(nxt, prev), (prev, nxt)]:
                one = reading(rule, a, b, ns, forward, backward)
                two = breadth_first_reading(rule[1], a, b, ns, forward, backward)
                require(one == two, f'Configuration matchers disagree: {name}')
                source_tests += 1
                require(one is None or not set(one[ring:]) <= ball,
                        f'Tested configuration core occurs in the union: {name}')

    hit = fixture['source_occurrence']
    source = fixture['configuration_source']
    raw = (here / hit['configuration']).read_bytes()
    require(sha256(raw).hexdigest() == source['sha256'], 'Positive source changed')
    require(sha256((here / 'LICENSE').read_bytes()).hexdigest() == source['license_sha256'],
            'Source licence changed')
    require(source['revision'] == json.loads((here / 'sources.json').read_text())['revision'],
            'Positive and baseline catalogue revisions differ')
    validate(read_rows(raw.decode()))
    rule, rows = source_rule(here, hit['configuration'])
    n, ring = rows[0]
    images = hit['images']
    require(len(images) == len(set(images)) == n, 'Positive occurrence is not injective')
    require(hit['orientation'] in ('source', 'reverse'), 'Unknown orientation')
    forward, backward = (nxt, prev) if hit['orientation'] == 'source' else (prev, nxt)
    a, b = [images[i - 1] for i in rule[1][0][1:3]]
    require(reading(rule, a, b, ns, forward, backward) == images,
            'Positive configuration matching failed')
    require(breadth_first_reading(rule[1], a, b, ns, forward, backward) == images,
            'Independent positive matching failed')
    require(all(images[i % ring] in ns[images[i - 1]] for i in range(1, ring + 1)),
            'Ordered boundary cycle is not preserved')
    core_rows = {a: set(vs) for a, _, *vs in rows[1:]}
    for a, degree, *vs in rows[1:]:
        require(len(ns[images[a - 1]]) == degree and
                ns[images[a - 1]] == {images[v - 1] for v in vs}, 'Full star differs')
        for b in core_rows:
            require((images[b - 1] in ns[images[a - 1]]) == (b in core_rows[a]),
                    'Positive core has an extra ambient edge')
    require(set(images[ring:]) <= ball, 'Positive core lies outside the union')
    return {
        'evidence': 'Independent exact program replay; no Lean certification.',
        'claim_tested': 'Flat seven-centres in a spherical triangulation of degrees 5..7 '
                        'need not form an acyclic graph, even without obstructing cycles of length 3..5.',
        'vertices': len(ns), 'faces': len(faces), 'edge_flips': prefix,
        'centres': centres, 'degrees': [len(ns[v]) for v in centres], 'charges': charges,
        'facial_triangle': True, 'short_cycles_checked': cycle_checks,
        'obstructing_short_cycles': 0, 'independent_rule_tests': tests,
        'joint_radius_two_vertices': len(ball), 'simple_core_hits': core_hits,
        'tested_configuration_sources': source_hashes, 'configuration_tests': source_tests,
        'tested_configuration_hits': 0,
        'positive_occurrence': {'configuration': hit['configuration'], 'core_vertices': n - ring,
            'ordered_boundary_ports': ring, 'core_radius': max(min(d[v] for d in distance) for v in images[ring:]),
            'complete_radius': max(min(d[v] for d in distance) for v in images),
            'injective_induced_core': True, 'reducibility_reproved_here': False},
        'not_claimed': ['Flatness of every vertex in the radius-three neighbourhoods',
                       'A counterexample to the exact SevenPairSector continuation theorem',
                       'Failure of every existing reduction or of compositional Four Colour proofs'],
        'rule_revision': revision, 'transfers': transfers,
        'shared_core_comparison': verify_core_map(here),
        'fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', default='flat-seven-return-example.json',
                        choices=['flat-seven-return-example.json',
                                 'flat-seven-return-extension-example.json'])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent, args.fixture)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'transfers'}, indent=2))
