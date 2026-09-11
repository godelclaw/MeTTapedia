#!/usr/bin/env python3
"""Calibrate an incidence-triple colouring trace before its coverage proof.

Pre-registered controls: K4 has 6 labelled Tait colourings, K3,3 has 12,
and Petersen has none. Compare vertex-wise permutation propagation with
the existing independent edge-colouring enumerators. Reindexing vertices,
edges, and positions must preserve the count. These are code checks, not
a base census or an unavoidable configuration catalogue.
"""

import itertools
import json
import random

import networkx as nx

from v24_absolute_topology_gate import enumerated


def encode(n, edges):
    stars = [[] for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        if u == v or not (0 <= u < n and 0 <= v < n):
            raise ValueError("invalid edge endpoints")
        stars[u].append(e)
        stars[v].append(e)
    if any(len(s) != 3 for s in stars):
        raise ValueError("not cubic")
    return tuple(tuple(s) for s in stars)


def assignments(stars, m):
    """One permutation of the three colours at each vertex, joined on edges."""
    if any(len(s) != 3 or len(set(s)) != 3 for s in stars):
        raise ValueError("invalid vertex triple")
    if sorted(e for s in stars for e in s) != sorted(list(range(m)) * 2):
        raise ValueError("each edge must occur twice")
    result = set()
    partial = [-1] * m

    def visit(v):
        if v == len(stars):
            assert -1 not in partial
            result.add(bytes(partial))
            return
        star = stars[v]
        for colours in itertools.permutations(range(3)):
            if any(partial[e] not in (-1, c) for e, c in zip(star, colours)):
                continue
            changed = [e for e in star if partial[e] == -1]
            for e, c in zip(star, colours):
                partial[e] = c
            visit(v + 1)
            for e in changed:
                partial[e] = -1

    visit(0)
    return result


def gate():
    bridge = nx.MultiGraph([(0, 1), (0, 2), (1, 2), (1, 2), (0, 3),
                           (3, 4), (3, 5), (4, 5), (4, 5)])
    controls = [("K4", nx.complete_graph(4), 6),
                ("K33", nx.complete_bipartite_graph(3, 3), 12),
                ("Petersen", nx.petersen_graph(), 0),
                ("bridged", bridge, 0)]
    rng = random.Random(41)
    receipt = []
    for name, graph, expected in controls:
        edges = sorted(tuple(sorted(e)) for e in graph.edges())
        stars = encode(len(graph), edges)
        actual = assignments(stars, len(edges))
        independent = set(enumerated(len(graph), edges))
        assert actual == independent and len(actual) == expected
        for _ in range(12):
            order = list(range(len(edges)))
            rng.shuffle(order)
            changed = [[order[e] for e in star] for star in stars]
            rng.shuffle(changed)
            for star in changed:
                rng.shuffle(star)
            recoded = assignments(changed, len(edges))
            assert {bytes(c[order[e]] for e in range(len(edges)))
                    for c in recoded} == actual
        receipt.append(dict(name=name, vertices=len(graph), edges=len(edges),
                            colourings=len(actual), reindexings=12,
                            planar=nx.check_planarity(graph)[0]))
    return {"controls": receipt, "status": "pass",
            "scope": "Exact incidence-code tests; no finite-base verification."}


if __name__ == "__main__":
    print(json.dumps(gate(), indent=2, sort_keys=True))
