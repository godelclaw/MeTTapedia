#!/usr/bin/env python3
"""Independently check merge semantics and literal diamond ear extensions.

Finite program evidence only; the arbitrary-length theorems are checked by
Lean. Graph colourings are enumerated independently of the boundary relation.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path

from diamond_coloring_alternatives import colorings, support
from probe_diamond_joint_repair import GEOMETRY, GEOMETRY_SHA256, ROOT, literal_graph
from probe_diamond_kempe import grammar, matches

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def negate(word, depth=0):
    if not word:
        return ''
    head, tail = word[0], word[1:]
    if head == '[':
        return head + negate(tail, depth + 1)
    if head == 's':
        return head + negate(tail, depth)
    if depth:
        return head + negate(tail, depth - 1)
    return ('1' if head == '0' else '0') + tail


def flip(word, depth=0):
    if not word:
        return '['
    head, tail = word[0], word[1:]
    if head == '[':
        return head + flip(tail, depth + 1)
    if head == 's':
        return head + flip(tail, depth)
    if depth:
        return head + flip(tail, depth - 1)
    return '[' + (negate(tail) if head == '0' else tail)


def merge(word):
    head, tail = word[:2], word[2:]
    if head in ('s[', '[s'):
        return '[' + negate(tail)
    if head == '[1':
        return 's' + tail
    if head == '[[':
        return 's' + flip(tail)
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.suffix != '.json':
        raise SystemExit('The output must be a JSON report.')
    raw = (ROOT / GEOMETRY).read_bytes()
    assert sha256(raw).hexdigest() == GEOMETRY_SHA256
    cases = 0
    for length in range(2, 10):
        for word in grammar(length):
            expected = {(t[0] ^ t[1],) + t[2:] for t in matches(word) if t[0] != t[1]}
            result = merge(word)
            actual = matches(result) if result is not None else set()
            assert expected == actual
            cases += 1
    rows = []
    for ordinal in (1, 2, 4):
        graph, boundary = literal_graph(raw.decode(), ordinal)
        vertices, values = colorings(graph)
        for ears in range(1, 4):
            before = support(vertices, values, boundary)
            u, v = boundary[:2]
            fresh = max(graph) + 1
            graph = {x: set(neighbours) for x, neighbours in graph.items()}
            assert v in graph[u]
            graph[fresh] = {u, v}
            graph[u].add(fresh)
            graph[v].add(fresh)
            boundary = [u, fresh, *boundary[1:]]
            expected_colorings = set()
            for value in values:
                colours = dict(zip(vertices, value))
                available = set(range(4)) - {colours[u], colours[v]}
                assert len(available) == 2
                expected_colorings.update(value + (c,) for c in available)
            vertices, values = colorings(graph)
            assert values == expected_colorings
            actual = support(vertices, values, boundary)
            predicted = {(a, b) + t[1:] for t in before for a in (1, 2, 3)
                         for b in (1, 2, 3) if a != b and a ^ b == t[0]}
            assert actual == predicted
            rows.append(dict(core=ordinal, ears=ears, vertices=len(vertices),
                             boundary=len(boundary), normalized_colourings=len(values),
                             boundary_traces=len(actual)))
    paths = [GEOMETRY, Path(__file__).resolve().relative_to(ROOT),
             Path('tools/fourcolor/classical/diamond_coloring_alternatives.py'),
             Path('tools/fourcolor/classical/probe_diamond_joint_repair.py'),
             Path('tools/fourcolor/classical/probe_diamond_kempe.py')]
    report = dict(evidence='Independent finite program checks; general theorems are in Lean.',
                  merge_chromograms=cases, graph_cases=rows,
                  source_sha256={str(p): sha256((ROOT / p).read_bytes()).hexdigest() for p in paths},
                  scope='Retained-edge ears, not boundary-triangle subdivisions or longer diamond fans.')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(merge_chromograms=cases, graph_cases=len(rows))))


if __name__ == '__main__':
    main()
