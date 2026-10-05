#!/usr/bin/env python3
"""Replay adjacent completion and the backward insertion experiment.

The eight-port majority repair and ten-port one-component obstruction have
separate Lean proofs. Backward pruning is exploratory program evidence;
no pruning table is exported as a proof certificate.
"""
import argparse
from functools import lru_cache
from itertools import combinations, permutations, product
import json
from pathlib import Path

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_fan import PROGRAM, verify as verify_source
from generate_exceptional_repair import boundary, pairings, traces


def code(word):
    return sum(c << (2*i) for i, c in enumerate(word))


@lru_cache(None)
def domain(n):
    words = traces(n)
    indices = {code(tuple(p[c-1] for c in w)): i
               for i, w in enumerate(words) for p in permutations((1, 2, 3))}
    return words, indices


@lru_cache(None)
def masks(active, fixed):
    rows = []
    for layout in pairings(len(active)):
        out = [0]
        for a, b in layout:
            mask = (fixed << (2*active[a])) | (fixed << (2*active[b]))
            out += [x ^ mask for x in out]
        rows.append(out)
    return rows


def trim(n, bad):
    """Largest remaining set stable against the abstract matching game."""
    words, indices = domain(n)
    bad, layers = set(bad), []
    while True:
        removed = []
        for i in sorted(bad):
            word, encoded = words[i], code(words[i])
            for fixed in (1, 2, 3):
                rows = masks(tuple(j for j, c in enumerate(word) if c != fixed), fixed)
                if not any(all(indices[encoded ^ m] in bad for m in row) for row in rows):
                    removed.append(i)
                    break
        if not removed:
            return bad, layers
        layers.append(len(removed))
        bad.difference_update(removed)


@lru_cache(None)
def insert(word, rotation, arity):
    word = word[rotation:] + word[:rotation]
    colours = boundary(word)
    answers = []
    for fresh in range(4):
        if fresh in colours[:arity]:
            continue
        new = [colours[0], fresh, *colours[arity-1:]]
        answers.append(tuple(a ^ b for a, b in zip(new, new[1:] + new[:1])))
    return tuple(answers)


def backward():
    n = 7
    words, indices = domain(n)
    bad = {i for i, w in enumerate(words) if len(set(boundary(w))) == 4}
    bad, layers = trim(n, bad)
    stages = [{'stage': 7, 'boundary': n, 'classes': len(words),
               'bad': len(bad), 'removed_layers': layers}]
    for stage, (_, rotation, arity) in reversed(list(enumerate(PROGRAM))):
        old_n = n + arity - 3
        old_words, old_indices = domain(old_n)
        preimage = {i for i, w in enumerate(old_words)
                    if all(indices[code(o)] in bad for o in insert(w, rotation, arity))}
        bad, layers = trim(old_n, preimage)
        stages.append({'stage': stage, 'boundary': old_n, 'classes': len(old_words),
                       'preimage_bad': len(preimage), 'bad': len(bad), 'removed_layers': layers})
        n, words, indices = old_n, old_words, old_indices
    require(not bad, 'Backward game retained an obstruction')
    return {'status': 'program evidence only', 'stages': stages,
            'limits': ['Pruning rounds are not yet replaced by structural Lean laws.',
                       'No physical move count or geometric occurrence supply is inferred.']}


def pair_fits(b):
    n = len(b)
    return any(x not in (b[n-2], b[n-1], b[0], b[1]) and y != x and
               all(y != b[i] for i in range(1, n-1))
               for x, y in product(range(4), repeat=2))


def guard_realized(here):
    _, adj = graph((here / 'D0099.conf').read_bytes())
    retained = set(range(19)) - {13, 15}
    ports = verify_source(here)['insertions'][5]['boundary']
    word = (3, 2, 2, 2, 2, 2, 3, 2)
    colours = dict(zip(ports, boundary(word)))
    require(all(colours[a] != colours[b] for a in colours for b in adj[a] & colours.keys()),
            'Guard is already improper on the retained source')

    def visit(todo):
        if not todo:
            return True
        v = max(todo, key=lambda x: (len(adj[x] & colours.keys()), x))
        for c in set(range(4)) - {colours[u] for u in adj[v] & colours.keys()}:
            colours[v] = c
            if visit(todo - {v}):
                return True
            del colours[v]
        return False

    require(visit(retained - colours.keys()), 'Guard has no actual source-prefix colouring')
    require(all(colours[a] != colours[b] for a in retained for b in adj[a] & retained),
            'Prefix witness is improper')
    return True


def verify(here, run_backward):
    source = verify_source(here)
    rows = []
    for n in (6, 8, 10):
        word = (3,) + (2,)*(n-3) + (3, 2)
        good = set()
        for pair in combinations(range(n), 2):
            out = tuple(c ^ 1 if i in pair else c for i, c in enumerate(word))
            if pair_fits(boundary(out)):
                good.add(pair)
        layouts = pairings(n)
        bad = [p for p in layouts if not set(p) & good]
        require(len(bad) == (1 if n == 10 else 0), 'Unexpected one-component obstruction count')
        rows.append({'boundary': n, 'successful_pairs': sorted(good),
                     'noncrossing_matchings': len(layouts), 'uncovered_matchings': len(bad)})
    obstruction = ((0, 3), (1, 2), (4, 9), (5, 8), (6, 7))
    require(obstruction in bad, 'Ten-port counterexample differs')
    report = {'status': 'local closing and one-component limit replayed',
              'source_sha256': source['source_sha256'], 'local_checks': rows,
              'ten_port_obstruction': obstruction,
              'actual_source_prefix_guard_realized': guard_realized(here),
              'limits': ['The six-port row is program evidence; the Lean consumer uses eight ports.',
                         'The ten-port result concerns one component in the displayed palette and matching.',
                         'Universal supply of the eight-port guard is not established.']}
    if run_backward:
        report['backward_experiment'] = backward()
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backward', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(verify(Path(__file__).resolve().parent, args.backward), indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')
