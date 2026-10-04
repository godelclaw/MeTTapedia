#!/usr/bin/env python3
"""Test physical repairs on D0092 exteriors with additional vertices.

All simple eleven-port disk triangulations with one labelled interior vertex
and either fixed boundary word are enumerated. Larger disks are a seeded
sample obtained by facial insertions, valid diagonal flips, and switches
avoiding the boundary. Every successful history is replayed on actual
components and checked against a full ambient colouring. No universal
repair-depth theorem or minimum-counterexample hypothesis is claimed.
"""
import argparse
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import random

from audit_boundary_observation import components, proper, switch
from audit_cycle_blocks import sphere
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_two_port_core import eliminate
from probe_pair_preparation import triangulations


def canonical(word):
    palette = {}
    return tuple(palette.setdefault(c, len(palette)) for c in word)


def one_hidden_disks(word):
    """The interior vertex's cyclic neighbours partition the remaining disk
    into polygons. Triangulate each gap without adding further vertices."""
    def fillings(u, v):
        gap = [j % 11 for j in range(u, v + 1)]
        if len(gap) == 2:
            return [()]
        result = []
        for faces in triangulations(0, len(gap) - 1):
            actual = tuple(tuple(gap[i] for i in face) for face in faces)
            if all(len({word[x] for x in face}) == 3 for face in actual):
                result.append(actual)
        return result

    for colour in range(4):
        eligible = [i for i, c in enumerate(word) if c != colour]
        for degree in range(3, len(eligible) + 1):
            for neighbours in combinations(eligible, degree):
                cyclic = list(zip(neighbours, neighbours[1:] + (neighbours[0] + 11,)))
                if any(word[u] == word[v % 11] for u, v in cyclic):
                    continue
                options = [fillings(u, v) for u, v in cyclic]
                centre = tuple((u, v % 11, 18) for u, v in cyclic)
                for chosen in product(*options):
                    yield colour, neighbours, centre + tuple(f for fs in chosen for f in fs)


def darts(faces):
    result = {}
    for i, (a, b, c) in enumerate(faces):
        for u, v, w in [(a, b, c), (b, c, a), (c, a, b)]:
            require((u, v) not in result, 'Repeated directed edge')
            result[u, v] = (i, w)
    return result


def flip(faces, colouring, rng):
    edges = darts(faces)
    candidates = list(edges)
    rng.shuffle(candidates)
    for a, b in candidates:
        if (b, a) not in edges:
            continue
        i, c = edges[a, b]
        j, d = edges[b, a]
        if c == d or (c, d) in edges or (d, c) in edges or colouring[c] == colouring[d]:
            continue
        result = list(faces)
        result[i], result[j] = (c, d, b), (d, c, a)
        return result
    return faces


def hidden_switch(faces, colouring, rng):
    adj = {v: set() for face in faces for v in face}
    for a, b in darts(faces):
        adj[a].add(b)
        adj[b].add(a)
    moves = [(pair, support) for pair in combinations(range(4), 2)
             for support in components(adj, colouring, pair) if not support & set(range(11))]
    if not moves:
        return colouring
    pair, support = rng.choice(moves)
    return switch(adj, colouring, pair, min(support))[0]


def verify(here, sampled_per_size):
    fixture = json.loads((here / 'core-profile-switch-example.json').read_text())
    raw = (here / 'D0092.conf').read_bytes()
    require(sha256(raw).hexdigest() == fixture['source']['sha256'], 'Source pin differs')
    ring, patch = graph(raw)
    require(ring == 11, 'Wrong source ring')

    @lru_cache(None)
    def extends(word):
        return eliminate(patch, ring, word)[0] is not None

    def shortest(adj, initial, limit=3):
        vertices = sorted(adj)
        require(vertices[:11] == list(range(11)), 'Port order differs')
        start = tuple(initial[v] for v in vertices)
        require(not extends(start[:11]), 'Initial word already extends')
        seen, frontier = {canonical(start)}, [(start, [])]
        for _ in range(limit):
            next_frontier = []
            for word, route in frontier:
                colouring = dict(zip(vertices, word))
                for a, b in combinations(range(4), 2):
                    for support in components(adj, colouring, (a, b)):
                        after = tuple((b if c == a else a) if v in support else c
                                      for v, c in zip(vertices, word))
                        signature = canonical(after)
                        if signature in seen:
                            continue
                        seen.add(signature)
                        path = route + [(a, b, min(support))]
                        if extends(after[:11]):
                            return path, len(seen)
                        next_frontier.append((after, path))
            frontier = next_frontier
        return None, len(seen)

    def check(faces, initial):
        ambient = sphere([tuple(f) for f in fixture['source_inner_faces']] +
                         [(a, c, b) for a, b, c in faces])
        require(all(ambient[v] == patch[v] for v in range(11, 18)), 'Changed source core star')
        adj = {v: ns - set(range(11, 18)) for v, ns in ambient.items() if v not in range(11, 18)}
        proper(adj, initial)
        path, visited = shortest(adj, initial)
        require(path is not None, 'A tested exterior needs more than three switches: ' +
                json.dumps({'faces': faces, 'initial': initial}))
        current = dict(initial)
        for a, b, root in path:
            current, _ = switch(adj, current, (a, b), root)
        core, _ = eliminate(patch, ring, tuple(current[j] for j in range(ring)))
        require(core is not None, 'Replayed history does not extend')
        proper(ambient, current | core)
        return len(path), visited

    exhaustive = []
    for index, word in enumerate(fixture['initial']):
        degrees, depths = Counter(), Counter()
        max_visited = 0
        for colour, neighbours, faces in one_hidden_disks(word):
            depth, visited = check(faces, dict(enumerate(word)) | {18: colour})
            degrees[len(neighbours)] += 1
            depths[depth] += 1
            max_visited = max(max_visited, visited)
        exhaustive.append({'word_index': index, 'colouring_exterior_pairs': sum(depths.values()),
                           'hidden_vertex_degrees': dict(sorted(degrees.items())),
                           'minimum_physical_steps': dict(sorted(depths.items())),
                           'maximum_visited_palette_classes': max_visited})
    require([r['colouring_exterior_pairs'] for r in exhaustive] == [3280, 3326],
            'One-interior-vertex enumeration changed')

    rng = random.Random(401019)
    seeds = json.loads((here / 'pair-preparation-probe.json').read_text())['results']
    samples = []
    for count in [2, 4, 8, 16, 32]:
        depths, max_visited = Counter(), 0
        for trial in range(sampled_per_size):
            seed = seeds[trial % 2]['largest_repair_example']
            faces = [tuple(f) for f in seed['faces']]
            colouring = dict(enumerate(seed['initial']))
            for v in range(18, 18 + count):
                a, b, c = faces.pop(rng.randrange(len(faces)))
                colouring[v] = next(iter(set(range(4)) - {colouring[a], colouring[b], colouring[c]}))
                faces.extend([(a, b, v), (b, c, v), (c, a, v)])
                for _ in range(3):
                    faces = flip(faces, colouring, rng)
            for _ in range(10 * count):
                faces = flip(faces, colouring, rng)
                if rng.random() < 0.1:
                    colouring = hidden_switch(faces, colouring, rng)
            depth, visited = check(faces, colouring)
            depths[depth] += 1
            max_visited = max(max_visited, visited)
        samples.append({'hidden_vertices': count, 'trials': sampled_per_size,
                        'minimum_physical_steps': dict(sorted(depths.items())),
                        'maximum_visited_palette_classes': max_visited})
    return {'classification': 'BOUNDED_PROGRAM_EVIDENCE', 'source': fixture['source'],
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
            'one_hidden_vertex': exhaustive, 'sample_seed': 401019, 'larger_samples': samples,
            'checks': ['Oriented spherical triangulation', 'Exact unchanged source core stars',
                       'Proper complete exterior colouring', 'Actual component-history replay',
                       'Exact ear elimination and full ambient colouring'],
            'limits': ['No universal three-switch theorem.',
                       'Larger samples can include repeated graphs or colourings; trial counts are not distinct graph counts.',
                       'No claim of minimal-counterexample connectivity or geometric occurrence supply.',
                       'Shortest-depth search quotients by global colour permutation on the entire exterior, not boundary summaries.']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sampled-per-size', type=int, default=300)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    require(args.sampled_per_size >= 0, 'Negative sample size')
    result = json.dumps(verify(Path(__file__).resolve().parent, args.sampled_per_size), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
