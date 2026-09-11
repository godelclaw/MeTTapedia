#!/usr/bin/env python3
"""Test a bounded-interface branching alternative to corridor generation.

Pre-registered checks:
* Every binary union tree with small leaves and a large root has a
  subtree of intermediate size. This must hold for every tree shape,
  not just a caterpillar or a balanced construction.
* The explicit split-grid control has no small full cut with two large
  sides. Branching therefore cannot hide the ambient interface.

This tests generic composition, not colourings, reducibility certificates,
or a population of hypothetical counterexamples.
"""

from functools import lru_cache
from itertools import combinations, permutations
import json


@lru_cache(None)
def shapes(n):
    if n == 1:
        return (None,)
    return tuple((a, b) for i in range(1, n)
                 for a in shapes(i) for b in shapes(n - i))


def supports(shape, leaves):
    it = iter(leaves)

    def visit(t):
        if t is None:
            value = next(it)
            return value, [value]
        a, sa = visit(t[0])
        b, sb = visit(t[1])
        return a | b, [a | b] + sa + sb

    return visit(shape)


def split_grid(n):
    side = n + 1

    def vertex(i, j, bit):
        return 2 * (i * side + j) + bit

    edges = [(vertex(i, j, 0), vertex(i, j, 1))
             for i in range(side) for j in range(side)]
    edges += [(vertex(i, j, 1), vertex(i, j + 1, 0))
              for i in range(side) for j in range(n)]
    edges += [(vertex(i, j, 1), vertex(i + 1, j, 0))
              for i in range(n) for j in range(side)]
    return 2 * side * side, edges


def cut_size(edges, mask):
    return sum(((mask >> u) ^ (mask >> v)) & 1 for u, v in edges)


def run():
    tree_checks = 0
    # All ordered full binary tree shapes and all leaf orderings, through 5.
    for n in range(1, 6):
        for shape in shapes(n):
            for order in permutations(range(n)):
                root, nodes = supports(shape, [1 << i for i in order])
                assert root.bit_count() == n
                for threshold in range(1, n):
                    assert any(threshold < s.bit_count() <= 2 * threshold
                               for s in nodes)
                    tree_checks += 1

    # Non-singleton and overlapping atoms: the balancing fact needs only
    # union subadditivity, not a disjoint partition assumption.
    overlap_checks = 0
    atoms = [0b00111, 0b01110, 0b11100, 0b10001]
    for shape in shapes(4):
        for order in permutations(atoms):
            root, nodes = supports(shape, order)
            threshold = 3
            assert root.bit_count() > threshold
            assert any(threshold < s.bit_count() <= 2 * threshold for s in nodes)
            overlap_checks += 1

    n = 2
    size, edges = split_grid(n)
    k = 1
    threshold = 2 * k * k + k
    assert size > 3 * threshold
    intermediate = []
    checked = 0
    for cardinality in range(threshold + 1, 2 * threshold + 1):
        for selected in combinations(range(size), cardinality):
            mask = sum(1 << i for i in selected)
            boundary = cut_size(edges, mask)
            assert boundary > k
            intermediate.append(boundary)
            checked += 1

    return {
        "tree_threshold_checks": tree_checks,
        "overlapping_atom_checks": overlap_checks,
        "split_grid": {
            "n": n, "vertices": size, "edges": len(edges), "width": k,
            "threshold": threshold, "intermediate_cuts_checked": checked,
            "minimum_intermediate_cut": min(intermediate),
        },
    }


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True))
