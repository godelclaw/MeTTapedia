#!/usr/bin/env python3
"""Test whether retained-cap controls suffice for actual source completion.

The terminal test reconstructs the six remaining core vertices. Leaving the
365-state residual set is not treated as success here. This is an untrusted
finite experiment; no strategy or failure table is emitted as a proof.
"""
import argparse
from collections import deque
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import time

from audit_cap_joint import SOURCE, analyze
from audit_cap_selector import ANCHORS, attractor
from audit_five_triangle_collapse import graph


@lru_cache(None)
def right_response(tail):
    """Joint colours at source vertices 13 and 17, retaining witnesses 16,18."""
    return tuple(sorted({(a, b) for a, b, c, d in product(range(4), repeat=4)
                         if a != tail[5] and b not in tail[:2]
                         and c not in tail[3:] and d not in tail[1:4]
                         and len({b, c, d}) == 3 and a != b and a != c}))


def inspect(data):
    # Check the relation's complete right-hand graph, including attachments.
    _, source = graph((SOURCE / 'D0099.conf').read_bytes())
    ports, core = [9, 10, 0, 1, 2, 3], [13, 17, 16, 18]
    assert [[i for i, p in enumerate(ports) if p in source[v]] for v in core] == [
        [5], [0, 1], [3, 4, 5], [1, 2, 3]]
    assert {(i, j) for i in range(4) for j in range(i + 1, 4)
            if core[j] in source[core[i]]} == {(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)}
    edges, states = data['edges'], data['states']
    width = len(edges)
    cap = [edges.index(e) for e in ANCHORS]
    transitions = [[set() for _ in range(3 * width)] for _ in states]
    adaptive = {'all': [], 'cap': []}
    for i, palettes in enumerate(data['layouts']):
        choices = {key: [] for key in adaptive}
        for fixed, layouts in enumerate(palettes):
            rows = {key: set() for key in adaptive}
            for components, targets in layouts:
                by_edge = {e: target for component, target in zip(components, targets)
                           for e in component}
                rows['all'].add(frozenset(targets))
                rows['cap'].add(frozenset(by_edge.get(e, i) for e in cap))
                for a in range(width):
                    transitions[i][fixed * width + a].add(by_edge.get(a, i))
            for key in adaptive:
                choices[key].append(rows[key])
        for key in adaptive:
            adaptive[key].append(choices[key])

    def fixed(pool):
        options = [[row[f * width + a] for f in range(3) for a in pool]
                   for row in transitions]
        rounds, remaining = attractor(options)
        return {'rounds': rounds, 'survivors': len(remaining)}

    def after_matching(choices):
        remaining, rounds = set(range(len(states))), []
        while True:
            removed = {i for i in remaining if any(
                all(not row <= remaining for row in palette) for palette in choices[i])}
            if not removed:
                return {'rounds': rounds, 'survivors': len(remaining)}
            remaining -= removed
            rounds.append(len(removed))

    # Reuse reverse dependencies for the bounded anchor-pool tests. This
    # computes the same least attractor, without repeating every round scan.
    arity = 3 * width
    counts, inverse = [], [[] for _ in states]
    for i, options in enumerate(transitions):
        for j, out in enumerate(options):
            counts.append(len(out - {-1}))
            for target in out - {-1}:
                inverse[target].append(i * arity + j)

    def survivors(pool):
        allowed = set(pool)
        pending, won = counts.copy(), set()
        queue = deque()
        for action, n in enumerate(pending):
            i = action // arity
            if not n and action % width in allowed and i not in won:
                won.add(i)
                queue.append(i)
        while queue:
            target = queue.popleft()
            for action in inverse[target]:
                i = action // arity
                if i in won or action % width not in allowed:
                    continue
                pending[action] -= 1
                if not pending[action]:
                    won.add(i)
                    queue.append(i)
        return len(states) - len(won)

    before = {'cap': fixed(cap), 'all': fixed(range(width))}
    assert before['cap']['survivors'] == survivors(cap) == 6223
    assert before['all']['survivors'] == survivors(range(width)) == 0
    after = {key: after_matching(choices) for key, choices in adaptive.items()}
    assert after['cap']['survivors'] == 5873 and after['all']['survivors'] == 0
    additions = [{'anchor': e, 'survivors': survivors([*cap, a])}
                 for a, e in enumerate(edges) if a not in cap]
    assert len(additions) == 15 and all(row['survivors'] for row in additions)
    pool = list(range(width))
    for a in range(width):
        candidate = [e for e in pool if e != a]
        if not survivors(candidate):
            pool = candidate
    assert not survivors(pool)
    assert all(survivors([e for e in pool if e != a]) for a in pool)

    def coarse(observed, pool, summary=None):
        groups, projection, rename = {}, [], []
        for state in states:
            col, names = dict(zip(data['vertices'], state)), {}
            signature = tuple(names.setdefault(col[v], len(names)) for v in observed)
            assert len(names) >= 3
            for c in range(4):
                names.setdefault(c, len(names))
            tail = tuple(names[col[v]] for v in ports)
            if summary == 'relation':
                signature = signature, right_response(tail)
            elif summary == 'lists':
                signature = signature, tuple(tuple(sorted(set(range(4)) - set(tail[a:b])))
                                             for a, b in ((0, 2), (1, 4), (3, 6)))
            elif summary == 'tail':
                signature = signature, tail
            if signature not in groups:
                groups[signature] = len(groups)
            projection.append(groups[signature])
            rename.append([names[0] ^ names[f] for f in (1, 2, 3)])
        options = [[set() for _ in range(3 * len(pool))] for _ in groups]
        for i, row in enumerate(transitions):
            for f in range(3):
                for j, a in enumerate(pool):
                    options[projection[i]][(rename[i][f] - 1) * len(pool) + j].update(
                        -1 if t == -1 else projection[t] for t in row[f * width + a])
        rounds, remaining = attractor(options)
        return {'observations': observed, 'profiles': len(groups),
                'rounds': rounds, 'survivors': len(remaining)}

    coarse_tests = []
    for observed in ([3, 4, 5, 6, 7, 8, 9, 11, 14], [3, 5, 7, 8, 9, 11, 14]):
        coarse_tests.append({'cap_anchors': coarse(observed, cap),
                             'all_anchors': coarse(observed, list(range(width)))})
    response_tests = []
    for observed in ([3, 4, 5, 6, 7, 8, 9, 11, 14], [3, 5, 7, 8, 9, 11, 14]):
        for summary in ('relation', 'lists', 'tail'):
            response_tests.append({'summary': summary,
                                   **coarse(observed, list(range(width)), summary)})
    assert [(r['profiles'], r['survivors']) for r in response_tests] == [
        (1800, 1455), (6444, 321), (7011, 0), (1225, 1081), (4097, 3718), (4446, 4023)]
    return {'anchor_before_matching': before, 'anchor_after_matching': after,
            'single_additional_anchor_tests': additions,
            'greedy_sufficient_pool': [edges[a] for a in pool],
            'greedy_scope': 'Inclusion-minimal in the tested full-state game; not a minimum-cardinality claim.',
            'coarse_tests': coarse_tests, 'right_response_tests': response_tests}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    report = analyze(inspect_components=inspect, direct_extension=True)
    assert report['prefix_states'] == 7011 and report['survivors'] == 0
    report['completion_verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    report['total_wall_seconds'] = time.monotonic() - start
    report['limits'] = [
        'This finite experiment is not a Lean repair theorem or a physical obstruction.',
        'The adversary can choose a new abstract exterior matching at each step.',
        'A single joined component can meet several original exterior components.',
        'The three-anchor rule escapes the smaller residual set but does not supply full continuation.',
        'No general lower bound on compositional proof size is established.',
        'No catalogue entry, original certificate or coverage obligation is removed.']
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
