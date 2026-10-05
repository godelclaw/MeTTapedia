#!/usr/bin/env python3
"""Explore the residual strip while retaining its five constructed triangles.

Untrusted bounded experiment. The external matching is on the original
eleven-edge boundary. Its paths are composed with the known triangular cap.
No proof or strategy table is emitted.
"""
import argparse
import json
import time
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path

SOURCE = Path(__file__).resolve().parent
from audit_five_triangle_collapse import graph
from audit_strip_fan_repair import code, domain, trim
from audit_strip_fan import SOURCE_SHA256, verify as verify_source
from audit_two_port_core import eliminate
from generate_exceptional_repair import boundary, pairings

PORTS = [4, 14, 11, 8, 9, 10, 0, 1, 2, 3]
VERTICES = [*range(12), 14]
HIDDEN = [5, 6, 7]
FACES = [(11, 6, 7), (11, 7, 8), (14, 4, 5), (14, 5, 6), (14, 6, 11)]


def edge(a, b):
    return tuple(sorted((a, b)))


def cycle(xs):
    return [edge(a, b) for a, b in zip(xs, xs[1:] + xs[:1])]


def canonical(col):
    labels = {}
    return tuple(labels.setdefault(col[v], len(labels)) for v in VERTICES)


def analyze(inspect_components=None):
    start = time.monotonic()
    source = verify_source(SOURCE)
    raw = (SOURCE / 'D0099.conf').read_bytes()
    assert sha256(raw).hexdigest() == SOURCE_SHA256
    _, adj = graph(raw)
    edges = sorted({edge(v, w) for v in VERTICES for w in adj[v] if w in VERTICES})
    edges_index = {e: i for i, e in enumerate(edges)}
    old_edges = [edges_index[e] for e in cycle(list(range(11)))]
    new_edges = [edges_index[e] for e in cycle(PORTS)]
    triangles = [[edges_index[e] for e in cycle(list(f))] for f in FACES]
    assert source['insertions'][1]['boundary'] == PORTS
    residual_vertices = PORTS + [12, 13, 15, 16, 17, 18]
    residual = [{residual_vertices.index(v) for v in adj[u] if v in residual_vertices}
                for u in residual_vertices]
    words, indices = domain(10)
    initially_bad = {i for i, word in enumerate(words)
                     if eliminate(residual, 10, boundary(word))[0] is None}
    bad, residual_rounds = trim(10, initially_bad)
    assert (len(words), len(words) - len(initially_bad), len(bad)) == (2461, 513, 365)
    states = set()
    for i in bad:
        visible = dict(zip(PORTS, boundary(words[i])))
        for hidden in product(range(4), repeat=3):
            col = visible | dict(zip(HIDDEN, hidden))
            if all(col[a] != col[b] for a, b in edges):
                states.add(canonical(col))
    states = sorted(states)
    state_index = {s: i for i, s in enumerate(states)}
    assert len(states) == 1377
    choices = []
    component_choices = []
    matchings = answers = 0
    closed_cycle_histogram = Counter()
    for state in states:
        col = dict(zip(VERTICES, state))
        labels = [col[a] ^ col[b] for a, b in edges]
        palettes = []
        component_palettes = []
        for fixed in (1, 2, 3):
            active_old = [i for i in old_edges if labels[i] != fixed]
            active_new = {i for i in new_edges if labels[i] != fixed}
            fixed_links = []
            for face in triangles:
                active = [i for i in face if labels[i] != fixed]
                assert len(active) == 2
                fixed_links.append(active)
            layouts = []
            component_layouts = []
            for matching in pairings(len(active_old)):
                network = {i: set() for i in range(len(edges)) if labels[i] != fixed}
                for a, b in fixed_links + [[active_old[a], active_old[b]] for a, b in matching]:
                    network[a].add(b)
                    network[b].add(a)
                assert all(len(ns) == (1 if i in active_new else 2) for i, ns in network.items())
                components = []
                todo = set(network)
                while todo:
                    root = min(todo)
                    component, pending = {root}, [root]
                    while pending:
                        for v in network[pending.pop()] - component:
                            component.add(v)
                            pending.append(v)
                    todo -= component
                    assert len(component & active_new) in (0, 2)
                    components.append(component)
                chords = [sorted(new_edges.index(i) for i in c & active_new)
                          for c in components if c & active_new]
                assert all(not (a < c < b < d or c < a < d < b)
                           for a, b in chords for c, d in chords)
                closed_cycle_histogram[sum(not c & active_new for c in components)] += 1
                masks = [set()]
                for component in components:
                    masks += [mask | component for mask in masks]
                outcomes = set()
                single_targets = []
                for selection, mask in enumerate(masks):
                    changed = [c ^ fixed if i in mask else c for i, c in enumerate(labels)]
                    old_word = [changed[i] for i in old_edges]
                    new_col = dict(enumerate(boundary(old_word)))
                    new_col[11] = new_col[8] ^ changed[edges_index[edge(8, 11)]]
                    new_col[14] = new_col[4] ^ changed[edges_index[edge(4, 14)]]
                    assert all(new_col[a] ^ new_col[b] == changed[i] for i, (a, b) in enumerate(edges))
                    trace = tuple(changed[i] for i in new_edges)
                    if indices[code(trace)] not in bad:
                        target = -1
                    else:
                        target = state_index[canonical(new_col)]
                    outcomes.add(target)
                    if inspect_components is not None and selection and not selection & (selection - 1):
                        single_targets.append(target)
                layouts.append(frozenset(outcomes))
                if inspect_components is not None:
                    assert len(single_targets) == len(components)
                    component_layouts.append((components, single_targets))
                matchings += 1
                answers += len(masks)
            palettes.append(set(layouts))
            if inspect_components is not None:
                component_palettes.append(component_layouts)
        choices.append(palettes)
        if inspect_components is not None:
            component_choices.append(component_palettes)

    remaining = set(range(len(states)))
    ranks = {}
    rounds = []
    while True:
        removed = {i for i in remaining
                   if any(not any(out <= remaining for out in palette) for palette in choices[i])}
        if not removed:
            break
        remaining -= removed
        rounds.append(len(removed))
        ranks.update((i, len(rounds)) for i in removed)
    def profile(state, vertices):
        labels = {}
        col = dict(zip(VERTICES, state))
        return tuple(labels.setdefault(col[v], len(labels)) for v in vertices)
    profiles = {}
    for name, vertices in [('cap', [4, 5, 6, 7, 8, 11, 14]),
                           ('old_cap', [4, 5, 6, 7, 8]),
                           ('rest', [8, 9, 10, 0, 1, 2, 3, 4])]:
        groups = {}
        for i, state in enumerate(states):
            groups.setdefault(profile(state, vertices), Counter())[ranks.get(i, -1)] += 1
        profiles[name] = {'classes': len(groups),
                          'mixed_rank_classes': sum(len(x) > 1 for x in groups.values()),
                          'rank_signatures': sorted({tuple(sorted(v)) for v in groups.values()})}
    pairs = list(combinations(range(len(VERTICES)), 2))
    equality = [sum(1 << j for j, (a, b) in enumerate(pairs) if s[a] == s[b]) for s in states]
    sufficient = []
    for size in range(1, len(VERTICES) + 1):
        for selected in combinations(range(len(VERTICES)), size):
            mask = sum(1 << j for j, (a, b) in enumerate(pairs) if a in selected and b in selected)
            seen = {}
            for i, signature in enumerate(equality):
                key = signature & mask
                if key in seen and seen[key] != ranks.get(i, -1):
                    break
                seen[key] = ranks.get(i, -1)
            else:
                sufficient.append({'vertices': [VERTICES[v] for v in selected], 'classes': len(seen)})
        if sufficient:
            break
    common_equalities = [(VERTICES[a], VERTICES[b]) for a, b in pairs
                         if all(s[a] == s[b] for s in states)]
    observed = [3, 4, 5, 6, 7, 8, 9, 11, 14]
    signatures = sorted({profile(state, observed) for state in states})
    signature_index = {s: i for i, s in enumerate(signatures)}
    projection = [signature_index[profile(state, observed)] for state in states]
    quotient = [[set() for _ in range(3)] for _ in signatures]
    for i, state in enumerate(states):
        colors = dict(zip(VERTICES, state))
        names = {}
        for v in observed:
            names.setdefault(colors[v], len(names))
        for c in range(4):
            names.setdefault(c, len(names))
        for fixed, layouts in enumerate(choices[i], 1):
            renamed = names[0] ^ names[fixed]
            quotient[projection[i]][renamed - 1].update(
                frozenset(-1 if x == -1 else projection[x] for x in answer) for answer in layouts)
    quotient_remaining = set(range(len(signatures)))
    quotient_rounds = []
    while True:
        removed = {i for i in quotient_remaining
                   if any(not any(out <= quotient_remaining for out in palette) for palette in quotient[i])}
        if not removed:
            break
        quotient_remaining -= removed
        quotient_rounds.append(len(removed))
    assert not remaining and not quotient_remaining
    assert len(signatures) == 51
    report = {'evidence': 'Program game evidence; the cap reconstruction law is separately Lean checked.',
            'source_sha256': SOURCE_SHA256,
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
            'forgotten_cap_game': {'states': len(words), 'direct': len(words)-len(initially_bad),
                                  'survivors': len(bad), 'rounds': residual_rounds},
            'retained_prefix_states': len(states), 'cap_faces': FACES,
            'external_boundary': 11, 'residual_boundary': 10,
            'matchings_composed': matchings, 'batch_assignments': answers,
            'closed_cap_component_histogram': dict(closed_cycle_histogram),
            'pruning_rounds': rounds, 'survivors': len(remaining),
            'local_rank_profiles': profiles,
            'smallest_observation_sets_for_computed_rank': sufficient,
            'common_equalities': common_equalities,
            'quotient_game': {'observations': observed, 'states': len(signatures),
                              'transition_sets': sum(len(x) for qs in quotient for x in qs),
                              'rounds': quotient_rounds, 'survivors': len(quotient_remaining),
                              'interpretation': 'One palette per visible profile must handle every hidden completion and matching.'},
            'sample_survivors': [states[i] for i in sorted(remaining)[:3]],
            'wall_seconds': time.monotonic() - start,
            'limits': ['Known triangular paths are retained, but matching choices are still adversarial.',
                       'No physical exterior realization is inferred.',
                       'No strategy table is exported or counted as compression.',
                       'The Lean transport law does not certify the pruning or the 51-profile selector.',
                       'Actual progress, source completion, strict reduction and coverage remain separate obligations.']}
    if inspect_components is not None:
        report['selector_experiment'] = inspect_components({
            'states': states, 'vertices': VERTICES, 'edges': edges,
            'layouts': component_choices, 'observations': observed,
            'profiles': signatures, 'projection': projection, 'ranks': ranks})
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = analyze()
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
