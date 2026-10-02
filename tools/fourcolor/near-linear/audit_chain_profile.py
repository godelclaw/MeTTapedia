#!/usr/bin/env python3
"""Replay the whole-neighbourhood example that selects the chain repair.

Checks exact local charge twice, the complete source occurrence, and both
sides of every short cycle. These are program checks; the Lean module
certifies the occurrence and reconstruction separately.
"""
import argparse
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_diamond_sources import read_rows, require
from probe_flat_pairs import geometry, read_rules, reading, breadth_first_reading


def verify(here):
    source = here / 'chain-profile-example.json'
    fixture = json.loads(source.read_text())
    faces = fixture['faces']
    darts, neighbors, nxt, prev = geometry(faces)
    require(len(neighbors) == 42 and len(faces) == 80, 'Fixture size differs')
    todo, seen = [0], {0}
    while todo:
        v = todo.pop()
        for w in neighbors[v] - seen:
            seen.add(w)
            todo.append(w)
    require(seen == set(neighbors), 'Disconnected graph')
    centres = fixture['centres']
    require(centres == [40, 18], 'Centres differ')
    require(len(neighbors[40]) == 8 and len(neighbors[18]) == 7, 'Centre degree differs')
    require({v for v in neighbors[40] if len(neighbors[v]) > 6} == {18}, 'High neighbours differ')
    require(all(5 <= len(row) <= 8 for row in neighbors.values()), 'Global degree bounds fail')
    rules, revision = read_rules(here)
    require(revision == fixture['rule_revision'], 'Rule revision differs')
    profiles, tests = [], 0
    for centre in centres:
        net, transfers = 0, []
        for other in sorted(neighbors[centre]):
            incoming, outgoing = [], []
            for a, b, hits, sign in [(other, centre, incoming, 1), (centre, other, outgoing, -1)]:
                for rule in rules:
                    one = reading(rule, a, b, neighbors, nxt, prev)
                    two = breadth_first_reading(rule[1], a, b, neighbors, nxt, prev)
                    require(one == two, 'Independent matchers disagree')
                    tests += 1
                    if one is not None:
                        amount = rule[1][0][3]
                        net += sign * amount
                        hits.append([rule[0], amount])
            transfers.append({'neighbour': other, 'incoming': incoming, 'outgoing': outgoing})
        charge = 10 * (6 - len(neighbors[centre])) + net
        require(charge == 0, 'Centre is not flat')
        profiles.append({'centre': centre, 'charge': charge, 'transfers': transfers})

    def ball(v):
        return {v} | neighbors[v] | set().union(*(neighbors[w] for w in neighbors[v]))

    balls = list(map(ball, centres))
    union = set.union(*balls)
    for a, b in darts:
        tips = [nxt[a, b], prev[a, b]]
        if {a, b, *tips} <= union:
            require(not (all(len(neighbors[v]) == 5 for v in [a, *tips]) and
                         len(neighbors[b]) in (5, 6)), 'Known diamond core occurs')

    # Cutting the dual face graph along a simple cycle identifies its actual sides.
    cycles = set()
    for start in neighbors:
        def visit(path):
            if len(path) >= 3 and start in neighbors[path[-1]]:
                cycles.add(min(tuple(path), (start, *reversed(path[1:]))))
            if len(path) == 5:
                return
            for w in neighbors[path[-1]]:
                if w > start and w not in path:
                    visit(path + [w])
        visit([start])
    for cyc in cycles:
        cut = {frozenset(e) for e in zip(cyc, cyc[1:] + cyc[:1])}
        remaining, sides = set(range(len(faces))), []
        while remaining:
            queue = deque([remaining.pop()])
            side = set(queue)
            while queue:
                tri = faces[queue.popleft()]
                for a, b in zip(tri, tri[1:] + tri[:1]):
                    if frozenset((a, b)) in cut:
                        continue
                    j = darts[b, a][0]
                    if j in remaining:
                        remaining.remove(j)
                        side.add(j)
                        queue.append(j)
            sides.append(set().union(*(set(faces[i]) for i in side)) - set(cyc))
        require(len(sides) == 2, 'Cycle did not have two sides')
        require(min(map(len, sides)) < (2 if len(cyc) == 5 else 1), 'Obstructing short cycle')

    manifest = json.loads((here / 'chain-sources.json').read_text())
    raw = (here / fixture['configuration']).read_bytes()
    require(sha256(raw).hexdigest() == manifest['files'][fixture['configuration']]['sha256'], 'Source hash differs')
    rows = read_rows(raw.decode())
    n, ring = rows[0]
    images = fixture['images']
    require(len(images) == n == len(set(images)), 'Occurrence is not injective')
    require(set(images[ring:]) <= balls[0], 'Core left first radius-two ball')
    require(all(images[(i + 1) % ring] in neighbors[images[i]] for i in range(ring)), 'Ring edge missing')
    for v, degree, *row in rows[1:]:
        a = images[v - 1]
        require(len(neighbors[a]) == degree, 'Prescribed degree differs')
        actual = [images[b - 1] for b in row]
        require(set(actual) == neighbors[a], 'Incomplete core star')
        require(all(nxt[a, b] == c for b, c in zip(actual, actual[1:] + actual[:1])), 'Core cyclic order differs')

    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/NearLinearChainExample.lean'
    text = lean.read_text()
    for v in neighbors:
        match = re.search(r'\| ' + str(v) + r' => ("[^\n]+")', text)
        require(match is not None, 'Lean row missing')
        row = read_rows(json.loads(match.group(1)))[0]
        require(set(row) == neighbors[v] and len(row) == len(neighbors[v]), 'Lean adjacency differs')
        require(all(nxt[v, a] == b for a, b in zip(row, row[1:] + row[:1])), 'Lean rotation differs')
    match = re.search(r'def image.*?:= !\[([^\]]+)\]', text)
    require(match is not None and [int(s.strip()) for s in match.group(1).split(',')] == images, 'Lean occurrence differs')
    return {'evidence': 'Independent program replay; not a Lean proof of coverage.',
            'vertices': len(neighbors), 'faces': len(faces), 'profiles': profiles,
            'independent_rule_tests': tests, 'short_cycles_checked': len(cycles),
            'obstructing_short_cycles': 0, 'radius_two_sizes': list(map(len, balls)),
            'radius_two_union_size': len(union), 'known_diamond_cores_in_union': 0,
            'source_core_vertices': n - ring, 'source_ring': ring,
            'all_source_vertices_distinct': True, 'complete_oriented_core_stars': True,
            'example_sha256': sha256(source.read_bytes()).hexdigest(),
            'lean_example_sha256': sha256(lean.read_bytes()).hexdigest(),
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
