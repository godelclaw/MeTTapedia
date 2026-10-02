#!/usr/bin/env python3
"""Replay the chain that crosses a flat pair's radius-two boundary.

Uses two independent rule matchers, all short cycles, a full source occurrence,
and the exact cyclic stars read by Lean. Program geometry remains distinct from
the kernel-certified local recognition and radius bound.
"""
import argparse
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_diamond_sources import require, read_rows
from generate_rule_traces import compile_traces
from probe_flat_pairs import geometry, initial_faces, read_rules, reading, breadth_first_reading


def subdivide(faces):
    edges = sorted({tuple(sorted((a, b))) for tri in faces
                    for a, b in zip(tri, tri[1:] + tri[:1])})
    size = max(max(t) for t in faces) + 1
    middle = {e: i + size for i, e in enumerate(edges)}
    result = []
    for a, b, c in faces:
        ab, bc, ca = (middle[tuple(sorted(e))] for e in ((a, b), (b, c), (c, a)))
        result += [(a, ab, ca), (b, bc, ab), (c, ca, bc), (ab, bc, ca)]
    return result


def distances(neighbors, centre):
    values, queue = {centre: 0}, deque([centre])
    while queue:
        for other in neighbors[vertex := queue.popleft()]:
            if other not in values:
                values[other] = values[vertex] + 1
                queue.append(other)
    require(set(values) == set(neighbors), 'Disconnected graph')
    return values


def short_cycles(faces, darts, neighbors):
    cycles = set()
    for start in neighbors:
        def visit(path):
            if len(path) >= 3 and start in neighbors[path[-1]]:
                cycles.add(min(tuple(path), (start, *reversed(path[1:]))))
            if len(path) == 5:
                return
            for other in neighbors[path[-1]]:
                if other > start and other not in path:
                    visit(path + [other])
        visit([start])
    for cycle in cycles:
        cut = {frozenset(e) for e in zip(cycle, cycle[1:] + cycle[:1])}
        remaining, sides = set(range(len(faces))), []
        while remaining:
            queue = [remaining.pop()]
            side = set(queue)
            while queue:
                tri = faces[queue.pop()]
                for a, b in zip(tri, tri[1:] + tri[:1]):
                    if frozenset((a, b)) in cut:
                        continue
                    j = darts[b, a][0]
                    if j in remaining:
                        remaining.remove(j)
                        side.add(j)
                        queue.append(j)
            sides.append(set().union(*(set(faces[i]) for i in side)) - set(cycle))
        require(len(sides) == 2, 'Cycle does not have two sides')
        require(min(map(len, sides)) < (2 if len(cycle) == 5 else 1),
                'Obstructing short cycle')
    return len(cycles)


def chain_rule(here):
    raw = (here / 'D0004.conf').read_bytes()
    manifest = json.loads((here / 'chain-sources.json').read_text())
    require(sha256(raw).hexdigest() == manifest['files']['D0004.conf']['sha256'],
            'Chain source hash differs')
    rows = read_rows(raw.decode())
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
    data = [[n, 9, 10, 0]]
    for a in range(1, n + 1):
        if a in core:
            degree, vs = core[a]
            data.append([a, degree, degree, *vs])
        else:
            data.append([a, 0, 0, *[x for b in sorted(adj[a]) for x in (b, -1)]])
    return ('D0004.conf', data, compile_traces(data)), rows


def verify(here):
    source = here / 'chain-boundary-example.json'
    fixture = json.loads(source.read_text())
    faces = subdivide(initial_faces())
    require(faces == list(map(tuple, fixture['initial_faces'])), 'Initial sphere differs')
    for a, b, c, d in fixture['edge_flip_history']:
        darts, neighbors, _, _ = geometry(faces)
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d) and d not in neighbors[c], 'Illegal edge flip')
        require(min(len(neighbors[a]), len(neighbors[b])) >= 6 and
                max(len(neighbors[c]), len(neighbors[d])) <= 7, 'Degree guard differs')
        faces[i], faces[j] = (c, d, b), (d, c, a)
    require(faces == list(map(tuple, fixture['faces'])), 'Flip replay differs')
    require(len(fixture['edge_flip_history']) == fixture['step'] == 100, 'Flip count differs')
    darts, neighbors, nxt, prev = geometry(faces)
    require(len(neighbors) == 162 and len(faces) == 320, 'Fixture size differs')
    require(all(5 <= len(vs) <= 8 for vs in neighbors.values()), 'Degree bounds fail')
    centres = fixture['centres']
    require(centres == [112, 16], 'Centres differ')
    require(len(neighbors[112]) == 8 and len(neighbors[16]) == 7, 'Centre degrees differ')
    require({v for v in neighbors[112] if len(neighbors[v]) > 6} == {16}, 'High neighbours differ')
    distance = [distances(neighbors, c) for c in centres]
    balls = [{v for v, d in values.items() if d <= 2} for values in distance]
    joint = set.union(*balls)
    rules, revision = read_rules(here)
    require(revision == fixture['rule_revision'], 'Rule revision differs')
    profiles, tests = [], 0
    for orientation, turns, backwards in [('source', nxt, prev), ('Lean', prev, nxt)]:
        for centre in centres:
            charge = 10 * (6 - len(neighbors[centre]))
            transfers = []
            for other in sorted(neighbors[centre]):
                for a, b, sign in ((other, centre, 1), (centre, other, -1)):
                    for rule in rules:
                        one = reading(rule, a, b, neighbors, turns, backwards)
                        two = breadth_first_reading(rule[1], a, b, neighbors, turns, backwards)
                        require(one == two, 'Rule matchers disagree')
                        tests += 1
                        if one is not None:
                            amount = sign * rule[1][0][3]
                            charge += amount
                            transfers.append([rule[0], a, b, amount, one])
            require(charge == 0, 'Centre is not flat')
            profiles.append({'orientation': orientation, 'centre': centre, 'charge': charge, 'transfers': transfers})
    for a, b in darts:
        tips = (nxt[a, b], prev[a, b])
        if {a, b, *tips} <= joint:
            require(not (len(neighbors[a]) == 5 and len(neighbors[b]) in (5, 6) and
                         all(len(neighbors[v]) == 5 for v in tips)), 'Diamond in joint ball')
        if len(neighbors[a]) == 6:
            for rot in (nxt, prev):
                word = [b]
                for _ in range(3):
                    word.append(rot[a, word[-1]])
                if {a, *word} <= joint:
                    require([len(neighbors[v]) for v in word] != [5, 6, 5, 5],
                            'Chain in joint ball')
    root = fixture['chain_root']
    require(root == [7, 81], 'Chain root differs')
    word = [root[1]]
    for _ in range(3):
        word.append(prev[root[0], word[-1]])
    core = [word[3], root[0], word[2], word[1], word[0]]
    require(core == fixture['chain_core'] == [79, 7, 78, 77, 81], 'Chain core differs')
    require(len(neighbors[7]) == 6 and [len(neighbors[v]) for v in word] == [5, 6, 5, 5],
            'Chain degree word differs')
    require(distance[0][7] == 2 and all(values[79] > 2 for values in distance),
            'Observation boundary is not crossed')
    rule, rows = chain_rule(here)
    images = reading(rule, 79, 7, neighbors, nxt, prev)
    require(images is not None and images == breadth_first_reading(rule[1], 79, 7, neighbors, nxt, prev),
            'Full chain occurrence fails')
    require(images[8:] == core and len(set(images)) == 13, 'Source core or injectivity differs')
    for a, degree, *vs in rows[1:]:
        require({images[v - 1] for v in vs} == neighbors[images[a - 1]], 'Incomplete core star')
    require(max(distance[0][v] for v in images) <= 4, 'Complete patch leaves radius four')
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/ChainBoundaryGeometry.lean'
    text = lean.read_text()
    for v in neighbors:
        match = re.search(r'\| ' + str(v) + r' => ("[^\n]+")', text)
        require(match is not None, 'Lean row missing')
        row = read_rows(json.loads(match.group(1)))[0]
        require(set(row) == neighbors[v] and len(row) == len(neighbors[v]), 'Lean adjacency differs')
        require(all(prev[v, a] == b for a, b in zip(row, row[1:] + row[:1])), 'Lean rotation differs')
    return {'evidence': 'Independent program replay; no universal coverage claim.',
            'vertices': len(neighbors), 'faces': len(faces), 'flips_replayed': fixture['step'],
            'profiles': profiles, 'independent_rule_tests': tests,
            'short_cycles_checked': short_cycles(faces, darts, neighbors),
            'obstructing_short_cycles': 0, 'radius_two_sizes': list(map(len, balls)),
            'radius_two_union_size': len(joint), 'diamond_cores_in_union': 0,
            'chain_cores_in_union_either_orientation': 0,
            'chain_core': core, 'complete_chain_images': images,
            'chain_centre_distance': distance[0][7],
            'crossing_vertex_distances': [values[79] for values in distance],
            'full_chain_max_distance': max(distance[0][v] for v in images),
            'example_sha256': sha256(source.read_bytes()).hexdigest(),
            'lean_geometry_sha256': sha256(lean.read_bytes()).hexdigest(),
            'lean_example_sha256': sha256(lean.with_name('ChainBoundaryExample.lean').read_bytes()).hexdigest(),
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


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
