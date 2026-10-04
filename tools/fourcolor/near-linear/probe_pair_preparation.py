#!/usr/bin/env python3
"""Vary triangulated exteriors for the two core-profile boundary words.

This is a bounded program test on eleven-port exteriors with no additional
vertices. The separate Lean source theorem rules out an entire fixed-pair
phase for the second word, with no bound on exterior size or topology.
"""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import switch, components, proper
from audit_cycle_blocks import sphere
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_two_port_core import eliminate


@lru_cache(None)
def triangulations(i, j):
    if j == i + 1:
        return ((),)
    return tuple(left + right + ((i, k, j),)
                 for k in range(i + 1, j)
                 for left in triangulations(i, k) for right in triangulations(k, j))


def verify(here):
    fixture = json.loads((here / 'core-profile-switch-example.json').read_text())
    raw = (here / 'D0092.conf').read_bytes()
    require(sha256(raw).hexdigest() == fixture['source']['sha256'], 'Source pin differs')
    ring, patch = graph(raw)
    require(ring == 11, 'Wrong source ring')

    @lru_cache(None)
    def extends(word):
        return eliminate(patch, ring, word)[0] is not None

    def step(adj, word, a, b, root):
        if word[root] not in (a, b):
            return tuple(word), []
        new, component = switch(adj, dict(enumerate(word)), (a, b), root)
        return tuple(new[v] for v in range(ring)), sorted(component)

    def canonical(word):
        palette = {}
        return tuple(palette.setdefault(c, len(palette)) for c in word)

    def shortest(adj, initial, limit=3):
        # Global palette permutations preserve properness, extension and the
        # full set of allowed Kempe commands. Concrete paths are still kept.
        visited = {canonical(initial)}
        frontier = [(tuple(initial), [])]
        for _ in range(limit):
            next_frontier = []
            for word, path in frontier:
                for a, b in combinations(range(4), 2):
                    for support in components(adj, dict(enumerate(word)), (a, b)):
                        command = [a, b, min(support)]
                        after, _ = step(adj, word, *command)
                        representative = canonical(after)
                        if representative in visited:
                            continue
                        visited.add(representative)
                        route = path + [command]
                        if extends(representative):
                            require(extends(after), 'Palette quotient lost extension')
                            return route, len(visited)
                        next_frontier.append((after, route))
            frontier = next_frontier
        return None, len(visited)

    results = []
    commands = [(a, b, root) for a, b in combinations(range(4), 2) for root in range(ring)]
    for index, word in enumerate(fixture['initial']):
        require(not extends(tuple(word)), 'The initial word already extends')
        counts = Counter()
        failure = None
        depths = Counter()
        largest = None
        max_visited = 0
        for faces in triangulations(0, ring - 1):
            adj = {v: set() for v in range(ring)}
            for face in faces:
                for u, v in combinations(face, 2):
                    adj[u].add(v)
                    adj[v].add(u)
            if any(word[u] == word[v] for u in adj for v in adj[u]):
                continue
            ambient = sphere([tuple(f) for f in fixture['source_inner_faces']] +
                             [(a, c, b) for a, b, c in faces])
            require(all(ambient[v] == patch[v] for v in range(ring, len(patch))),
                    'Core acquired extra neighbours')
            require(all(adj[v] == ambient[v] & set(range(ring)) for v in range(ring)),
                    'Exterior is not the induced graph')
            counts['proper_exteriors'] += 1
            after, _ = step(adj, word, 0, 3, 2)
            counts['fixed_switch_succeeds'] += extends(after)
            prepared, prep = step(adj, word, 1, 3, 4)
            final, last = step(adj, prepared, 0, 3, 2)
            counts['fixed_preparation_then_switch_succeeds'] += extends(final)
            counts['preparation_equals_first_word'] += prepared == tuple(fixture['initial'][0])
            counts['some_single_switch_succeeds'] += any(
                extends(step(adj, word, *command)[0]) for command in commands)
            if not extends(final) and failure is None:
                failure = {'faces': faces, 'initial': word, 'prepared': prepared,
                           'preparation_component': prep, 'after': final, 'final_component': last}
            route, visited = shortest(adj, word)
            max_visited = max(max_visited, visited)
            depth = len(route) if route is not None else None
            if route is not None:
                final = tuple(word)
                for command in route:
                    final, _ = step(adj, final, *command)
                core, _ = eliminate(patch, ring, final)
                require(core is not None, 'Concrete route does not extend')
                proper(ambient, dict(enumerate(final)) | core)
            depths[str(depth) if depth is not None else '>3'] += 1
            if depth is not None and (largest is None or depth > largest['depth']):
                largest = {'depth': depth, 'faces': faces, 'history': route, 'initial': word}
        results.append({'word_index': index, 'counts': dict(counts),
                        'failure_of_fixed_preparation': failure,
                        'minimum_physical_steps_up_to_three': dict(depths),
                        'maximum_visited_palette_classes': max_visited,
                        'largest_repair_example': largest})
    require(results[0]['counts']['proper_exteriors'] == 200, 'First domain count differs')
    require(results[1]['counts']['proper_exteriors'] == 199, 'Second domain count differs')
    require(results[1]['counts']['some_single_switch_succeeds'] == 0, 'One-step obstruction differs')
    require(results[1]['counts']['fixed_preparation_then_switch_succeeds'] == 12,
            'The tested preparation count differs')
    require(all('>3' not in r['minimum_physical_steps_up_to_three'] for r in results),
            'The three-step bounded observation changed')
    return {'classification': 'BOUNDED_PROGRAM_TEST',
            'polygon_triangulations': len(triangulations(0, ring - 1)), 'results': results,
            'scope': 'All triangulated exteriors with no vertices beyond the eleven ports and '
                     'each fixed word. These counts and the alternate failure fixtures are '
                     'program evidence, not a universal preparation or coverage theorem. Shortest-depth counts use palette-permutation canonicalization; paths retain concrete commands.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
