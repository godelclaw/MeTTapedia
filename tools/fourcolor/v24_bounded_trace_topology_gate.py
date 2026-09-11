#!/usr/bin/env python3
"""Check incidence-code connectivity and single-edge deletion semantics.

Pre-registered outcomes: K4, Petersen and three parallel edges are connected
and bridge-free; the joined doubled triangles are connected with one bridge;
two disjoint parallel triples are disconnected and bridge-free. This is a
topology-encoding gate, not a spherical-base audit.
"""

import json
import random

import networkx as nx

from v24_bounded_cubic_trace_gate import encode


def topology(stars, m):
    ends = [[] for _ in range(m)]
    for v, star in enumerate(stars):
        if len(star) != 3 or len(set(star)) != 3:
            raise ValueError("invalid cubic star")
        for e in star:
            if not 0 <= e < m:
                raise ValueError("invalid edge index")
            ends[e].append(v)
    if any(len(pair) != 2 for pair in ends):
        raise ValueError("an edge must have two distinct endpoints")

    def reached(start, removed=None):
        seen = {start}
        todo = [start]
        while todo:
            v = todo.pop()
            for e in stars[v]:
                if e == removed:
                    continue
                for w in ends[e]:
                    if w not in seen:
                        seen.add(w)
                        todo.append(w)
        return seen

    return {"connected": bool(stars) and len(reached(0)) == len(stars),
            "bridges": [e for e, (u, v) in enumerate(ends)
                        if v not in reached(u, e)]}


def gate():
    bridge = [(0, 1), (0, 2), (1, 2), (1, 2), (0, 3),
              (3, 4), (3, 5), (4, 5), (4, 5)]
    cases = [("K4", 4, list(nx.complete_graph(4).edges()), True, 0),
             ("Petersen", 10, list(nx.petersen_graph().edges()), True, 0),
             ("parallel3", 2, [(0, 1)] * 3, True, 0),
             ("bridged", 6, bridge, True, 1),
             ("disconnected", 4, [(0, 1)] * 3 + [(2, 3)] * 3, False, 0)]
    rng = random.Random(91)
    receipt = []
    for name, n, edges, connected, bridges in cases:
        stars = encode(n, edges)
        expected = topology(stars, len(edges))
        assert expected["connected"] == connected
        assert len(expected["bridges"]) == bridges
        graph = nx.MultiGraph()
        graph.add_nodes_from(range(n))
        for e, (u, v) in enumerate(edges):
            graph.add_edge(u, v, key=e)
        assert nx.is_connected(graph) == connected
        reference_bridges = []
        for e, (u, v) in enumerate(edges):
            removed = graph.copy()
            removed.remove_edge(u, v, e)
            if not nx.has_path(removed, u, v):
                reference_bridges.append(e)
        assert expected["bridges"] == reference_bridges
        for _ in range(12):
            order = list(range(len(edges)))
            rng.shuffle(order)
            changed = [[order[e] for e in star] for star in stars]
            rng.shuffle(changed)
            for star in changed:
                rng.shuffle(star)
            actual = topology(changed, len(edges))
            assert actual["connected"] == connected
            assert set(actual["bridges"]) == {order[e] for e in expected["bridges"]}
        receipt.append(dict(name=name, connected=connected, bridges=bridges,
                            reindexings=12))
    assert topology((), 0) == {"connected": False, "bridges": []}
    return {"status": "pass", "controls": receipt,
            "scope": "Incidence topology only; no spherical-base verification."}


if __name__ == "__main__":
    print(json.dumps(gate(), sort_keys=True, indent=2))
