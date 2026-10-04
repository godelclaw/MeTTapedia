#!/usr/bin/env python3
"""Replay a closing triangle outside the D0092-shaped catalogue family.

The catalogue directory must contain the D/*.conf files from the pinned
revision. This is independent program evidence, not a Lean proof or a
reducibility check. Complete source degrees and rotations are retained.
"""

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

import networkx as nx

from audit_chain_boundary import distances, short_cycles, subdivide
from audit_diamond_sources import read_rows, require, validate
from audit_seven_pair_example import source_rule, tested_cores
from probe_flat_pairs import (
    breadth_first_reading, geometry, initial_faces, read_rules, reading,
)


def internal(rows):
    vertices = {a for a, *_ in rows[1:]}
    edges = {tuple(sorted((a, b))) for a, _, *vs in rows[1:]
             for b in vs if b in vertices}
    faces = {tuple(sorted((a, b, c))) for a, _, *vs in rows[1:]
             for b, c in zip(vs, vs[1:] + vs[:1]) if b in vertices and c in vertices}
    graph = nx.Graph()
    graph.add_nodes_from(vertices)
    graph.add_edges_from(edges)
    return graph, faces


def strip(rows):
    """Return a triangle attachment sequence, checking each new vertex."""
    graph, faces = internal(rows)
    dual = nx.Graph()
    dual.add_nodes_from(faces)
    dual.add_edges_from((a, b) for a in faces for b in faces
                        if a < b and len(set(a) & set(b)) == 2)
    if not faces or not nx.is_tree(dual) or max(dict(dual.degree()).values()) > 2:
        return None
    ends = sorted(f for f, d in dual.degree() if d <= 1)
    path = nx.shortest_path(dual, ends[0], ends[-1])
    seen = set(path[0])
    for previous, face in zip(path, path[1:]):
        if len(set(face) - seen) != 1 or set(face) & seen != set(face) & set(previous):
            return None
        seen.update(face)
    edges = {tuple(sorted((a, b))) for face in path for a in face for b in face if a < b}
    if seen != set(graph) or edges != {tuple(sorted(e)) for e in graph.edges()}:
        return None
    return path


def catalogue_inventory(catalogue, fixture):
    paths = sorted(catalogue.glob('*.conf'))
    digest = sha256()
    decoded = {}
    for path in paths:
        raw = path.read_bytes()
        digest.update(f'{path.name} {sha256(raw).hexdigest()}\n'.encode())
        decoded[path.name] = read_rows(raw.decode())
        validate(decoded[path.name])
    pin = fixture['catalogue']
    require(len(paths) == pin['files'], 'Catalogue file count differs')
    require(digest.hexdigest() == pin['content_sha256'], 'Pinned catalogue content differs')
    base, _ = internal(decoded['D0092.conf'])
    family, strips, sizes = [], [], Counter()
    for name, rows in decoded.items():
        if any(degree > 7 for _, degree, *_ in rows[1:]):
            continue
        graph, _ = internal(rows)
        if len(graph) == 7 and nx.is_isomorphic(base, graph):
            family.append(name)
        if strip(rows) is not None:
            strips.append(name)
            sizes[len(graph)] += 1
    require(family == fixture['five_triangle_family'], 'Five-triangle inventory differs')
    require(len(strips) == fixture['strip_inventory_count'], 'Strip inventory differs')
    return decoded, family, strips, dict(sorted(sizes.items()))


def replay_faces(fixture):
    faces = subdivide(initial_faces())
    for a, b, c, d in fixture['edge_flip_history']:
        darts, neighbors, _, _ = geometry(faces)
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d) and d not in neighbors[c], 'Illegal edge flip')
        require(min(len(neighbors[a]), len(neighbors[b])) >= 6 and
                max(len(neighbors[c]), len(neighbors[d])) <= 6, 'Degree guard differs')
        faces[i], faces[j] = (c, d, b), (d, c, a)
    return faces


def verify(here, catalogue, fixture, decoded, family):
    faces = replay_faces(fixture)
    darts, ns, nxt, prev = geometry(faces)
    require(all((v, u) in darts for u, v in darts), 'Open surface edge')
    require(len(distances(ns, 0)) == len(ns) == 162, 'Connected sphere size differs')
    require(all(5 <= len(vs) <= 7 for vs in ns.values()), 'Ambient degree bounds fail')
    cycle_checks = short_cycles(faces, darts, ns)
    centres = fixture['centres']
    require(len(set(centres)) == 3 and any(set(f) == set(centres) for f in faces),
            'The centres do not bound one face')
    ds = [distances(ns, c) for c in centres]
    ball = {v for v in ns if min(d[v] for d in ds) <= 2}
    rules, revision = read_rules(here)
    require(revision == fixture['rule_revision'], 'Rule revision differs')
    rule_checks = 0
    charges = []
    for u in centres:
        require(len(ns[u]) == 7, 'A centre is not seven-valent')
        charge = -10
        for v in sorted(ns[u]):
            for a, b, sign in ((v, u, 1), (u, v, -1)):
                for rule in rules:
                    one = reading(rule, a, b, ns, nxt, prev)
                    require(one == breadth_first_reading(rule[1], a, b, ns, nxt, prev),
                            'Independent rule matchers disagree')
                    rule_checks += 1
                    if one is not None:
                        charge += sign * rule[1][0][3]
        require(charge == 0, 'A centre is not flat')
        charges.append(charge)
    require(not [(name, core) for name, core in tested_cores(ns, nxt, prev) if core <= ball],
            'A tested simple core occurs')
    source_checks = 0
    for name in family + fixture['other_configurations']:
        rule, rows = source_rule(catalogue, name)
        ring = rows[0][1]
        for a, b in sorted(darts):
            for fw, bw in ((nxt, prev), (prev, nxt)):
                one = reading(rule, a, b, ns, fw, bw)
                require(one == breadth_first_reading(rule[1], a, b, ns, fw, bw),
                        f'Independent configuration matchers disagree: {name}')
                source_checks += 1
                # Exclude even noninjective readings. Do not silently discard collisions.
                require(one is None or not set(one[ring:]) <= ball,
                        f'A tested core occurs in the joint ball: {name}')
    hit = fixture['source_occurrence']
    name = hit['configuration']
    require((here / name).read_bytes() == (catalogue / name).read_bytes(),
            'Vendored positive source differs from the pinned catalogue')
    rule, rows = source_rule(catalogue, name)
    n, ring = rows[0]
    images = hit['images']
    require(len(images) == len(set(images)) == n, 'Positive reading is not injective')
    require(hit['orientation'] in ('source', 'reverse'), 'Unknown orientation')
    fw, bw = (nxt, prev) if hit['orientation'] == 'source' else (prev, nxt)
    a, b = [images[i - 1] for i in rule[1][0][1:3]]
    require(reading(rule, a, b, ns, fw, bw) == images and
            breadth_first_reading(rule[1], a, b, ns, fw, bw) == images,
            'Positive occurrence differs')
    require(set(images[ring:]) <= ball, 'Positive core leaves the joint ball')
    require(all(ns[images[i - 1]] == {images[v - 1] for v in vs}
                for i, _, *vs in rows[1:]), 'Incomplete positive core star')
    require(all(images[i % ring] in ns[images[i - 1]] for i in range(1, ring + 1)),
            'Ordered boundary cycle differs')
    construction = strip(rows)
    require(construction is not None and len(construction) == 6,
            'Positive source is not a six-triangle strip')
    source_graph, _ = internal(decoded['D0092.conf'])
    target_graph, _ = internal(rows)
    mapping = {int(a): b for a, b in fixture['core_map'].items()}
    require(set(mapping) == set(source_graph) and len(set(mapping.values())) == 7,
            'Core map domain or injectivity differs')
    require(set(mapping.values()) == set(target_graph) - {fixture['new_ear']},
            'Core map misses the wrong vertex')
    require(all(source_graph.has_edge(a, b) == target_graph.has_edge(mapping[a], mapping[b])
                for a in source_graph for b in source_graph), 'Core adjacency differs')
    return {
        'evidence': 'Independent program checks; no Lean coverage or reducibility claim.',
        'vertices': len(ns), 'edges': len(darts) // 2, 'faces': len(faces),
        'centres': centres, 'charges': charges, 'joint_radius_two_vertices': len(ball),
        'nonobstructing_short_cycles_checked': cycle_checks,
        'independent_rule_comparisons': rule_checks,
        'absent_configurations': family + fixture['other_configurations'],
        'independent_configuration_comparisons': source_checks,
        'positive_configuration': name, 'positive_core_vertices': n - ring,
        'positive_boundary_ports': ring, 'triangle_attachment_sequence': construction,
        'core_map_preserves': 'Unlabelled internal adjacency only; no boundary or repair transfer.',
        'whole_flat_ball_claimed': False, 'all_planar_maps_covered': False,
        'catalogue_entries_removed': 0, 'certificate_dependencies_removed': 0,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalogue', type=Path, required=True, help='Pinned catalogue D directory')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    fixture_path = here / 'closing-triangle-strip-example.json'
    fixture = json.loads(fixture_path.read_text())
    pin = json.loads((here / 'sources.json').read_text())
    require(fixture['catalogue']['revision'] == pin['revision'], 'Catalogue revision differs')
    require(sha256((here / 'LICENSE').read_bytes()).hexdigest() ==
            pin['files']['LICENSE']['sha256'], 'Catalogue licence differs')
    decoded, family, strips, sizes = catalogue_inventory(args.catalogue, fixture)
    result = verify(here, args.catalogue, fixture, decoded, family)
    result.update({'catalogue_revision': pin['revision'], 'catalogue_files_checked': len(decoded),
                   'catalogue_strip_count': len(strips), 'strip_core_size_histogram': sizes,
                   'fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(),
                   'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()})
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
