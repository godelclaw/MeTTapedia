"""Check both colouring branches on literal diamond subdivisions.

Original colourings and contracted-graph colourings are enumerated separately.
Their extensions are compared with an independent enumeration of the target.
This is finite program evidence for the catalogue instances, separate from the
general Lean witness equivalence.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import time

from configuration_map_isomorphism import EXPECTED_HASHES, records
from diamond_subdivision_geometry import rows, subdivide, verify
from probe_diamond_star import INPUT_HASHES, full_support, orient

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def proper(adjacency, colors):
    return set(colors) == set(adjacency) and all(
        colors[v] in range(4) and colors[v] != colors[w]
        for v, ns in adjacency.items() for w in ns)


def colorings(adjacency):
    """Enumerate all colourings, with the first retained vertex fixed to zero."""
    vertices = sorted(adjacency)
    fixed = vertices[0]
    result = set()
    def visit(colors):
        if len(colors) == len(vertices):
            assert proper(adjacency, colors)
            result.add(tuple(colors[v] for v in vertices))
            return
        domains = {v: set(range(4)) - {colors[w] for w in adjacency[v] if w in colors}
                   for v in vertices if v not in colors}
        chosen = min(domains, key=lambda v: (len(domains[v]), -len(adjacency[v]), v))
        for color in sorted(domains[chosen]):
            visit(colors | {chosen: color})
    visit({fixed: 0})
    return vertices, result


def contracted(adjacency, a, b):
    image = lambda v: a if v == b else v
    result = {v: set() for v in adjacency if v != b}
    for v, ns in adjacency.items():
        for w in ns:
            if image(v) != image(w):
                result[image(v)].add(image(w))
    return result, image


def support(vertices, values, boundary):
    result = set()
    for value in values:
        colors = dict(zip(vertices, value))
        word = tuple(colors[v] ^ colors[w]
                     for v, w in zip(boundary, boundary[1:] + boundary[:1]))
        assert 0 not in word
        result.add(word)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--configurations', type=Path, required=True)
    parser.add_argument('--geometry', type=Path, required=True)
    parser.add_argument('--inputs', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    inputs = {args.configurations.resolve(), args.geometry.resolve()} | {
        (args.inputs / f'{i-1}.in').resolve() for i in INPUT_HASHES}
    assert args.output.resolve() not in inputs
    start = time.monotonic()
    raw = args.configurations.read_bytes()
    assert sha256(raw).hexdigest() == EXPECTED_HASHES['configurations']
    sources = records(raw.decode())
    geometry = json.loads(args.geometry.read_text())
    chosen = [row for row in geometry['successes']
              if (row['source'], row['target'], row['triangle']) in
              [(1, 2, [1, 2, 7]), (2, 4, [5, 6, 10])]]
    assert len(chosen) == 2
    reports = []
    for witness in chosen:
        first, second = witness['source'], witness['target']
        source, target = sources[first - 1], sources[second - 1]
        a, b, c = witness['triangle']
        before = rows(source)
        after, boundary, fresh = subdivide(source, a, b, c)
        verify(after, boundary, target, witness)
        small, image = contracted(before, a, b)
        old_vertices, old = colorings(before)
        small_vertices, merged = colorings(small)
        new_vertices, actual = colorings(after)
        unequal, equal = set(), set()
        for value in old:
            colors = dict(zip(old_vertices, value))
            available = set(range(4)) - {colors[a], colors[b], colors[c]}
            assert len(available) == 1
            coloring = colors | {fresh: next(iter(available))}
            assert proper(after, coloring) and coloring[a] != coloring[b]
            unequal.add(tuple(coloring[v] for v in new_vertices))
            assert not proper(after, colors | {fresh: colors[a]})
        for value in merged:
            colors = dict(zip(small_vertices, value))
            available = set(range(4)) - {colors[image(a)], colors[image(c)]}
            assert len(available) == 2
            lifted = {v: colors[image(v)] for v in before}
            for color in available:
                coloring = lifted | {fresh: color}
                assert proper(after, coloring) and coloring[a] == coloring[b]
                equal.add(tuple(coloring[v] for v in new_vertices))
            assert not proper(after, lifted | {fresh: lifted[a]})
        assert len(unequal) == len(old) and len(equal) == 2 * len(merged)
        assert unequal.isdisjoint(equal) and unequal | equal == actual
        assert unequal != actual and equal != actual
        expected_unequal = {value for value in actual
                            if value[new_vertices.index(a)] != value[new_vertices.index(b)]}
        assert unequal == expected_unequal
        left = support(new_vertices, unequal, boundary)
        right = support(new_vertices, equal, boundary)
        assert left.isdisjoint(right)
        n, stored, digest = full_support(args.inputs / f'{second-1}.in')
        assert digest == INPUT_HASHES[second]
        alignments = [dict(rotation=r, reflection=f) for r in range(n) for f in (False, True)
                      if orient(stored, r, f) == left | right]
        assert alignments
        reports.append(dict(source=first, target=second, triangle=[a,b,c],
            old_colorings=len(old), contracted_colorings=len(merged),
            unequal_colorings=len(unequal), equal_colorings=len(equal),
            target_colorings=len(actual), unequal_support=len(left),
            equal_support=len(right), target_support=len(left | right),
            stored_support_alignments=alignments,
            invalid_fresh_colors_rejected=len(old)+len(merged)))
    result = dict(evidence='Finite program checks of the catalogue instances.',
                  normalization='The least vertex is fixed to colour zero; full colouring counts are four times these counts.',
                  source_sha256=sha256(raw).hexdigest(),
                  geometry_sha256=sha256(args.geometry.read_bytes()).hexdigest(),
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  reports=reports, elapsed_seconds=round(time.monotonic()-start,3))
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
