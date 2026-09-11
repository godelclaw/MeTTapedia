#!/usr/bin/env python3
"""Exact Count gate for a two-vertex reconnection, not a patch catalogue.

Pre-registered checks: I+A=H+B on every four-port word, Q=A+B,
and a physical exterior for which I has zero Count but H has positive Count.
The physical control is intentionally outside the least-counterexample class:
I has a bridge and A is disconnected. No conclusion about planar 4CT follows.
Colour codes 1,2,3 are the nonzero Klein-group elements; 0 is also tested.
"""

from itertools import combinations, product
import json

import networkx as nx

from v24_absolute_topology_gate import enumerated


def proper(a, b, c):
    return 0 not in (a, b, c) and len({a, b, c}) == 3


def local_counts(w):
    i = sum(proper(w[0], w[1], z) and proper(w[2], w[3], z)
            for z in range(4))
    h = sum(proper(w[0], w[3], z) and proper(w[1], w[2], z)
            for z in range(4))
    a = int(0 not in w and w[0] == w[1] and w[2] == w[3])
    b = int(0 not in w and w[0] == w[3] and w[1] == w[2])
    q = sum(all(proper(w[j], x[(j-1) % 4], x[j]) for j in range(4))
            for x in product(range(1, 4), repeat=4))
    return dict(I=i, H=h, A=a, B=b, Q=q)


def control(name):
    edges = [(u+s, v+s) for s in (0, 4) for u, v in combinations(range(4), 2)
             if (u, v) != (0, 1)]
    more = {
        "A": (8, [(0, 1), (4, 5)]),
        "B": (8, [(0, 5), (1, 4)]),
        "I": (10, [(8, 9), (8, 0), (8, 1), (9, 4), (9, 5)]),
        "H": (10, [(8, 9), (8, 0), (8, 5), (9, 1), (9, 4)]),
        "Q": (12, [(8, 9), (9, 10), (10, 11), (11, 8),
                   (0, 8), (1, 9), (4, 10), (5, 11)]),
    }
    n, extra = more[name]
    return n, sorted(tuple(sorted(e)) for e in edges + extra)


def gate():
    words = list(product(range(4), repeat=4))
    for w in words:
        c = local_counts(w)
        assert c["I"] + c["A"] == c["H"] + c["B"]
        assert c["Q"] == c["A"] + c["B"]
        if 0 not in w and w[0] ^ w[1] ^ w[2] ^ w[3] == 0:
            assert bool(c["I"]) == (w[0] != w[1])
            assert bool(c["H"]) == (w[0] != w[3])
    results = {}
    for name, expected in dict(I=0, H=24, A=36, B=12, Q=48).items():
        n, edges = control(name)
        graph = nx.Graph(edges)
        assert len(edges) == len(set(edges)) == graph.number_of_edges()
        assert set(graph) == set(range(n))
        assert all(d == 3 for _, d in graph.degree())
        planar, embedding = nx.check_planarity(graph)
        assert planar
        embedding.check_structure()
        count = len(enumerated(n, edges))
        assert count == expected
        tensor_count = sum(4 * local_counts(w)["A"] * local_counts(w)[name]
                           for w in product(range(1, 4), repeat=4))
        assert count == tensor_count
        results[name] = dict(vertices=n, edges=[list(e) for e in edges], count=count,
                             connected=nx.is_connected(graph), planar=planar,
                             bridges=sorted(sorted(e) for e in nx.bridges(graph)))
    assert results["I"]["bridges"] == [[8, 9]]
    assert not results["A"]["connected"]
    assert results["H"]["connected"] and not results["H"]["bridges"]
    return dict(boundary_words_checked=len(words), controls=results,
                verdict="Two-vertex reconnection does not generally preserve zero Count.",
                scope="I has a bridge; this is not a least-counterexample specimen.")


if __name__ == "__main__":
    print(json.dumps(gate(), indent=2, sort_keys=True))
