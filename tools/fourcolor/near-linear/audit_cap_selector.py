#!/usr/bin/env python3
"""Test component selectors and observation loss on the retained D0099 cap.

Untrusted finite experiment. No strategy table or Lean certificate is emitted.
An action chooses a fixed edge anchor and a palette before the exterior matching
is known. All completions represented by an observation must permit progress.
"""
import argparse
import json
from hashlib import sha256
from itertools import combinations
from pathlib import Path

from audit_cap_joint import analyze

ANCHORS = [(3, 4), (8, 9), (11, 14)]


def attractor(choices):
    """Each action must succeed against every retained hidden completion."""
    remaining = set(range(len(choices)))
    rounds = []
    while True:
        removed = {q for q in remaining
                   if any(out and not out & remaining for out in choices[q])}
        if not removed:
            return rounds, remaining
        remaining -= removed
        rounds.append(len(removed))


def inspect(data):
    profiles, edges = data['profiles'], data['edges']
    count = len(profiles)
    profile_rank = {}
    for i, p in enumerate(data['projection']):
        rank = data['ranks'][i]
        assert profile_rank.setdefault(p, rank) == rank

    # A union of targets, rather than their intersection, gives the adversary
    # every matching and hidden completion consistent with the visible profile.
    transitions = {(p, a, f): set() for p in range(count)
                   for a in range(len(edges)) for f in (1, 2, 3)}
    for i, state in enumerate(data['states']):
        colors = dict(zip(data['vertices'], state))
        names = {}
        for v in data['observations']:
            names.setdefault(colors[v], len(names))
        assert len(names) >= 3
        for c in range(4):
            names.setdefault(c, len(names))
        p = data['projection'][i]
        for fixed, layouts in enumerate(data['layouts'][i], 1):
            f = names[0] ^ names[fixed]
            for components, targets in layouts:
                by_edge = {a: target for component, target in zip(components, targets)
                           for a in component}
                for a in range(len(edges)):
                    target = by_edge.get(a, i)  # An inactive anchor makes no change.
                    transitions[p, a, f].add(-1 if target == -1 else data['projection'][target])
    assert all(transitions.values())

    usable = [{a for a in range(len(edges)) if any(
        all(t == -1 or profile_rank[t] < profile_rank[p]
            for t in transitions[p, a, f]) for f in (1, 2, 3))} for p in range(count)]
    minimum_pools = []
    for size in range(1, len(edges) + 1):
        minimum_pools = [pool for pool in combinations(range(len(edges)), size)
                         if all(set(pool) & menu for menu in usable)]
        if minimum_pools:
            break
    assert [[edges[a] for a in pool] for pool in minimum_pools] == [ANCHORS]
    anchor_ids = [edges.index(e) for e in ANCHORS]

    def coarse_game(observed):
        groups, projection = {}, []
        for profile in profiles:
            col = dict(zip(data['observations'], profile))
            names = {}
            sig = tuple(names.setdefault(col[v], len(names)) for v in observed)
            if sig not in groups:
                groups[sig] = len(groups)
            projection.append(groups[sig])
        # Express the fixed palette as the XOR of two observed vertex colours.
        # This avoids choosing an arbitrary name for an unobserved colour.
        options = {(q, a, u, v): set() for q in range(len(groups))
                   for a in anchor_ids for u, v in combinations(observed, 2)}
        for p, profile in enumerate(profiles):
            col = dict(zip(data['observations'], profile))
            q = projection[p]
            for a in anchor_ids:
                for u, v in combinations(observed, 2):
                    f = col[u] ^ col[v]
                    out = transitions[p, a, f] if f else {p}
                    options[q, a, u, v].update(
                        -1 if t == -1 else projection[t] for t in out)
        choices = [[] for _ in groups]
        for (q, _, _, _), out in options.items():
            choices[q].append(out)
        rounds, remaining = attractor(choices)
        return {'observations': list(observed), 'profiles': len(groups),
                'rounds': rounds, 'survivors': len(remaining)}

    layers = []
    for size in range(len(data['observations']), 1, -1):
        rows = [coarse_game(obs) for obs in combinations(data['observations'], size)]
        winners = [row for row in rows if not row['survivors']]
        layers.append({'size': size, 'subsets_tested': len(rows),
                       'minimum_survivors': min(row['survivors'] for row in rows),
                       'successful_subsets': winners})
        if not winners:
            break
    assert [(row['size'], len(row['successful_subsets'])) for row in layers] == [
        (9, 1), (8, 4), (7, 1), (6, 0)]
    best = layers[-2]['successful_subsets'][0]
    assert best['observations'] == [3, 5, 7, 8, 9, 11, 14]
    assert best['profiles'] == 37 and len(best['rounds']) == 16
    return {'retained_states': len(data['states']), 'full_profiles': count,
            'anchors': ANCHORS,
            'minimum_anchor_pool_scope': 'Fixed anchors lowering the original computed rank; all eighteen prefix edges tested.',
            'minimum_anchor_pool_count': len(minimum_pools),
            'observation_tests': layers, 'smallest_successful_interface': best,
            'limits': [
                'All quantifiers range over the retained D0099 prefix states and abstract matchings.',
                'The adversary may choose a new hidden completion at each quotient step.',
                'Six-observation failure concerns memoryless fixed-anchor actions in this conservative quotient.',
                'It does not exclude history-dependent, matching-dependent or different geometric policies.',
                'Sixteen quotient rounds are not a physical runtime or component-switch bound.',
                'The progress ranks, domain and continuation are not Lean certified.',
                'No catalogue entry or certificate dependency is removed.']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    base = analyze(inspect_components=inspect)
    report = {'evidence': 'Finite program experiment, not a Lean proof.',
              'source_sha256': base['source_sha256'],
              'cap_verifier_sha256': base['verifier_sha256'],
              'selector_verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
              **base['selector_experiment']}
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
