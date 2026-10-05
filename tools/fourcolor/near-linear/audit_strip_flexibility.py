#!/usr/bin/env python3
"""Replay the flexibility obstruction and optionally the full matching game.

The two source inputs already have Lean repair theorems. The obstruction
concerns strictly increasing scores of evaluated relation cardinalities.
The optional seven-round census is an independent program check in the
universal noncrossing-matching model, not a Lean repair certificate or an
algorithmic bound for physical component switches.
"""
import argparse
import ast
from collections import Counter
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path
import re

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph, trace
from audit_independent_repair import complete_patch
from audit_two_port_core import eliminate
from audit_two_round_repair import matching
from generate_exceptional_repair import boundary, pairings, traces


def code(word):
    return sum(c << (2 * i) for i, c in enumerate(word))


def cardinalities(adj, word):
    assignment, state = eliminate(adj, 11, word)
    return assignment is not None, tuple(len(s['kept_relation']) for s in state['stages'])


def full_domain(adj):
    words = traces(11)
    indices = {}
    direct, features = [], []
    for i, w in enumerate(words):
        for p in permutations((1, 2, 3)):
            encoded = code(tuple(p[c - 1] for c in w))
            require(encoded not in indices or indices[encoded] == i, 'Palette classes overlap')
            indices[encoded] = i
        b = boundary(w)
        extends, sizes = cardinalities(adj, b)
        require(extends == (complete_patch(adj, b) is not None), 'Extension solvers disagree')
        direct.append(extends)
        unary = [4 - len({b[j] for j in adj[v] if j < 11}) for v in range(11, 19)]
        features.append((sum(sizes), sum(s * 17 ** (5 - j) for j, s in enumerate(sizes)),
                         sum(s * 17 ** j for j, s in enumerate(sizes)),
                         next((j for j, s in enumerate(sizes) if not s), 6),
                         sum(unary), sum(s * s for s in unary)))
    actions, layouts, successors = [], 0, 0
    for i, w in enumerate(words):
        palettes = []
        if not direct[i]:
            for fixed in (1, 2, 3):
                slots = [j for j, c in enumerate(w) if c != fixed]
                require(len(slots) % 2 == 0, 'Odd active boundary')
                rows = []
                for layout in pairings(len(slots)):
                    outcomes = [code(w)]
                    for a, b in layout:
                        mask = (fixed << (2 * slots[a])) | (fixed << (2 * slots[b]))
                        outcomes += [out ^ mask for out in outcomes]
                    targets = frozenset(indices[out] for out in outcomes)
                    rows.append(targets)
                    layouts += 1
                    successors += len(targets)
                palettes.append(rows)
        actions.append(palettes)

    def accepts(i, good):
        return any(all(any(good(j) for j in row) for row in rows) for rows in actions[i])

    names = ['sum_relation_cardinalities', 'forward_lex_relations', 'reverse_lex_relations',
             'nonempty_prefix_length', 'unary_sum', 'unary_square_sum']
    potentials = []
    for k, name in enumerate(names):
        successes = sum(accepts(i, lambda j: direct[j] or features[j][k] > features[i][k])
                        for i in range(len(words)) if not direct[i])
        potentials.append({'measure': name, 'strict_progress_inputs': successes,
                           'stalled_inputs': direct.count(False) - successes})
    rank = [0 if yes else -1 for yes in direct]
    layers = []
    while True:
        new = [i for i in range(len(words)) if rank[i] < 0 and accepts(i, lambda j: rank[j] >= 0)]
        if not new:
            break
        layers.append(len(new))
        for i in new:
            rank[i] = len(layers)
    relation_profiles, unary_profiles, deletions = Counter(), Counter(), Counter()
    for i, w in enumerate(words):
        if rank[i] != len(layers):
            continue
        b = boundary(w)
        relation_profiles[cardinalities(adj, b)[1]] += 1
        unary_profiles[tuple(4 - len({b[j] for j in adj[v] if j < 11})
                             for v in range(11, 19))] += 1
        count = 0
        for omitted in range(11, 19):
            vertices = [v for v in range(19) if v != omitted]
            index = {v: j for j, v in enumerate(vertices)}
            reduced = [{index[u] for u in adj[v] if u != omitted} for v in vertices]
            count += complete_patch(reduced, b) is not None
        deletions[count] += 1
    last_layer = {'rank': len(layers), 'classes': sum(relation_profiles.values()),
                  'relation_size_profiles': [{'sizes': k, 'count': v} for k, v in relation_profiles.items()],
                  'unary_size_profiles': [{'sizes': k, 'count': v} for k, v in unary_profiles.items()],
                  'deletion_repair_counts': dict(deletions)}
    return {'proper_boundary_classes': len(words), 'direct_extensions': sum(direct),
            'noncrossing_layouts': layouts, 'distinct_successors_per_layout_total': successors,
            'tested_potentials': potentials, 'newly_repaired_per_round': layers,
            'unresolved': rank.count(-1),
            'last_layer_discovery': last_layer,
            'scope': 'Every nonextending word has a palette for which every noncrossing matching has a batch reaching an earlier layer. This is a program check; neither source coverage in arbitrary maps nor a physical switch bound follows.'}


def verify(here, census=False):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82', 'Source pin changed')
    ring, adj = graph(raw)
    require((ring, len(adj)) == (11, 19), 'Unexpected graph dimensions')
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    source = lean / 'StripFlexibilityBarrier.lean'
    text = source.read_text()
    block = (lean / 'StripCriticalChain.lean').read_text().split('def boundary')[1].split('def step')[0]
    inputs = [tuple(map(int, re.findall(r'c([0-3])', row)))
              for row in re.findall(r'=> !\[([^]]+)\]', block)]
    def rows(name, end):
        chunk = text.split('def ' + name + ' :')[1].split(end)[0]
        values = re.findall(r'\| (?:false|true) => (.*?)(?=\n  \| |\Z)', chunk, re.S)
        return [ast.literal_eval(v.replace('!', '')) for v in values]
    chords = rows('chord', 'def mate')
    mates = rows('mate', 'def normalized')
    require(len(inputs) == len(chords) == len(mates) == 2, 'Input arity changed')
    results = []
    for s, b in enumerate(inputs):
        extends, initial = cardinalities(adj, b)
        require(not extends and initial == (3, 2, 2, 2, 1, 0), 'Critical-chain input changed')
        w = trace(b, ring)
        for p, fixed in enumerate((1, 2, 3)):
            pairs = matching(w, fixed, mates[s][p])
            require(len(chords[s][p]) == 5, 'Batch slot count changed')
            require({tuple(e) for e in chords[s][p] if e[0] != e[1]} == set(pairs),
                    'Batch slots do not cover exactly the matching')
            vectors = set()
            for bits in product((False, True), repeat=5):
                updated = list(b)
                for chosen, (a, d) in zip(bits, chords[s][p]):
                    if chosen:
                        updated = [c ^ fixed if a < i <= d else c for i, c in enumerate(updated)]
                changed = trace(updated, ring)
                matching(changed, fixed, mates[s][p])
                require(all((w[a] == w[d]) == (changed[a] == changed[d]) for a, d in pairs),
                        'Original chromogram parity changed')
                extends, sizes = cardinalities(adj, updated)
                require(not extends and complete_patch(adj, updated) is None, 'A batch extends')
                require(all(a <= d for a, d in zip(sizes, initial)), 'A relation size increases')
                vectors.add(sizes)
            results.append({'input': s, 'fixed_colour': fixed, 'chords': pairs,
                            'batch_masks_checked': 32, 'relation_size_vectors': sorted(vectors)})
    result = {'status': 'independent obstruction replay passed', 'source': 'D0099.conf',
              'source_sha256': sha256(raw).hexdigest(),
              'lean_source_sha256': sha256(source.read_bytes()).hexdigest(),
              'initial_boundaries': inputs, 'initial_relation_sizes': [3, 2, 2, 2, 1, 0],
              'cases': results, 'batch_masks_checked': 192,
              'limits': ['No common physical exterior realizing all three matchings is asserted.',
                         'Nonmonotone scores, neutral steps and further retained information remain possible.',
                         'The existing compatible repair of both inputs is preserved.']}
    if census:
        result['full_domain_program_check'] = full_domain(adj)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full-domain', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = verify(Path(__file__).resolve().parent, args.full_domain)
    payload = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
