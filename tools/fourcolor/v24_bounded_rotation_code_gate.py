#!/usr/bin/env python3
"""Calibrate a finite rotation code before proving spherical trace coverage.

Pre-registered controls: K4 has two spherical rotations among its sixteen
vertex-orientation choices; three parallel edges have two spherical and two
toroidal rotations. K3,3 and Petersen have no spherical rotation. Relabelling
darts must preserve the cycle count, including singleton face cycles.
This is a representation check, not a bounded Four-Color base audit.
"""

import itertools
import json
import math
import random

import networkx as nx

from v24_bounded_cubic_trace_gate import encode


def rotation(stars, m, signs):
    positions = [[] for _ in range(m)]
    for v, star in enumerate(stars):
        for i, edge in enumerate(star):
            positions[edge].append(3 * v + i)
    if any(len(p) != 2 for p in positions):
        raise ValueError("each edge must have two darts")
    alpha = [None] * (3 * len(stars))
    for a, b in positions:
        alpha[a], alpha[b] = b, a
    rho = [3 * v + (i + (1 if signs[v] else -1)) % 3
           for v in range(len(stars)) for i in range(3)]
    return alpha, rho


def cycle_count(perm):
    if sorted(perm) != list(range(len(perm))):
        raise ValueError("not a permutation")
    unseen = set(range(len(perm)))
    count = 0
    while unseen:
        x = min(unseen)
        count += 1
        while x in unseen:
            unseen.remove(x)
            x = perm[x]
    return count


def face_count(alpha, rho):
    return cycle_count([rho[alpha[d]] for d in range(len(alpha))])


def raw_code_count(bound):
    """Count the raw carrier arithmetically; do not enumerate its elements."""
    return sum(sum(m ** (3 * n) for m in range(3 * bound // 2 + 1)) *
               math.factorial(3 * n) ** 2 for n in range(bound + 1))


def gate():
    cases = [("K4", 4, list(nx.complete_graph(4).edges()), 2),
             ("parallel3", 2, [(0, 1)] * 3, 2),
             ("K33", 6, list(nx.complete_bipartite_graph(3, 3).edges()), 0),
             ("Petersen", 10, list(nx.petersen_graph().edges()), 0)]
    rng = random.Random(114)
    receipt = []
    for name, n, edges, expected_spheres in cases:
        stars = encode(n, edges)
        eulers = {}
        last = None
        for signs in itertools.product((False, True), repeat=n):
            alpha, rho = rotation(stars, len(edges), signs)
            faces = face_count(alpha, rho)
            euler = n - len(edges) + faces
            eulers[euler] = eulers.get(euler, 0) + 1
            last = (alpha, rho, faces)
        assert eulers.get(2, 0) == expected_spheres
        alpha, rho, faces = last
        for _ in range(12):
            order = list(range(3 * n))
            rng.shuffle(order)
            ca = [None] * len(order)
            cr = [None] * len(order)
            for d in range(len(order)):
                ca[order[d]] = order[alpha[d]]
                cr[order[d]] = order[rho[d]]
            assert face_count(ca, cr) == faces
        receipt.append(dict(name=name, vertices=n, edges=len(edges),
                            rotations=2 ** n,
                            euler_histogram={str(k): v for k, v in eulers.items()},
                            reindexings=12))
    assert cycle_count([0, 1, 2]) == 3
    assert cycle_count([1, 0, 2]) == 2
    assert cycle_count([]) == 0
    assert [raw_code_count(b) for b in range(3)] == [1, 38, 411610900]
    return {"status": "pass", "controls": receipt,
            "raw_code_counts": {str(b): raw_code_count(b) for b in range(4)},
            "scope": "Rotation and face-count encoding; no base audit."}


if __name__ == "__main__":
    print(json.dumps(gate(), sort_keys=True, indent=2))
