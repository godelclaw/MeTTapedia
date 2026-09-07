#!/usr/bin/env python3
"""Structural gate for two-patch common-core gluing on an ordered row.

Preregistered implication: if the closed neighborhoods of two deleted
adjacent vertex pairs are disjoint, their induced complements cover every
ambient edge and every incident pair of edges.  Consequently literal
common-core agreement is enough for the existing atlas gluing theorem.
Disjoint deleted pairs alone are NOT predicted to suffice.

Supplier: in a graph of maximum degree d, the twice-closed neighborhood of
an edge's ends has at most 2*(d+1)^2 vertices.  More than 4*(d+1)^2 row
sites with separately injective endpoint maps supply a separated second
site.  Full ambient edges, including shortcuts off the row, are used.

No edge colourings, configuration certificates, or target-counterexample
claims are involved.  The exhaustive labelled four-vertex graph count is
64; the labelled cubic six-vertex count is 70 (60 six-cycles plus ten
disjoint triangle pairs, by complementation).
"""

import argparse
import itertools
import json
import random


def neighbors(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def close(adj, vertices):
    return set(vertices).union(*(adj[v] for v in vertices))


def coverage(edges, first, second):
    retained = [{e for e in edges if not set(e) & pair}
                for pair in (set(first), set(second))]
    edge_cover = set(edges) <= retained[0] | retained[1]
    adjacent_cover = all(
        any(e in patch and f in patch for patch in retained)
        for e, f in itertools.combinations(edges, 2) if set(e) & set(f)
    )
    return edge_cover, adjacent_cover


def check_graph(n, edges, counts):
    adj = neighbors(n, edges)
    counts["graphs"] += 1
    for first, second in itertools.combinations(edges, 2):
        separated = close(adj, first).isdisjoint(close(adj, second))
        covered = coverage(edges, first, second)
        assert separated == all(covered), (n, edges, first, second, covered)
        counts["pair_comparisons"] += 1
        counts["separated_pairs"] += int(separated)
    return adj


def exhaustive(n, counts):
    possible = list(itertools.combinations(range(n), 2))
    cubic = 0
    accepted = 0
    for mask in range(1 << len(possible)):
        edges = [e for i, e in enumerate(possible) if mask >> i & 1]
        adj = neighbors(n, edges)
        if max(map(len, adj), default=0) > 3:
            continue
        check_graph(n, edges, counts)
        accepted += 1
        cubic += int(all(len(a) == 3 for a in adj))
    return {"vertices": n, "subcubic_graphs": accepted, "cubic_graphs": cubic}


def long_row(seed):
    """A Hamiltonian row with all edges of an ambient cubic graph retained."""
    n = 80
    rng = random.Random(seed)
    edges = {tuple(sorted((i, (i + 1) % n))) for i in range(n)}
    for _ in range(10000):
        order = list(range(n))
        rng.shuffle(order)
        matching = {tuple(sorted(order[i:i + 2])) for i in range(0, n, 2)}
        if not matching & edges:
            edges |= matching
            break
    else:
        raise AssertionError("deterministic matching search exhausted")
    adj = neighbors(n, edges)
    assert all(len(a) == 3 for a in adj)
    sites = [(i, i + 1) for i in range(65)]
    records = []
    for source in sites:
        forbidden = close(adj, close(adj, source))
        assert len(forbidden) <= 32
        blocked = [i for i, edge in enumerate(sites) if set(edge) & forbidden]
        assert len(blocked) <= 2 * len(forbidden)
        target = next(edge for edge in sites if not set(edge) & forbidden)
        assert close(adj, source).isdisjoint(close(adj, target))
        assert all(coverage(sorted(edges), source, target))
        # A boundary encounter is already local to the target: an edge from
        # its first endpoint to a port, followed by a common-core edge.
        # No path from the source deletion is used.
        port = next(v for v in sorted(adj[target[0]]) if v != target[1])
        far = next(v for v in sorted(adj[port]) if v not in target)
        common_edge = tuple(sorted((port, far)))
        exposed_edge = tuple(sorted((target[0], port)))
        assert common_edge in edges and exposed_edge in edges
        assert not set(common_edge) & (set(source) | set(target))
        assert not set(exposed_edge) & set(source)
        records.append(len(forbidden))
    return {"seed": seed, "vertices": n, "edges": len(edges),
            "sources": len(sites), "local_boundary_germs": len(records),
            "max_forbidden": max(records)}


def run():
    counts = {"graphs": 0, "pair_comparisons": 0, "separated_pairs": 0}
    census = [exhaustive(n, counts) for n in (4, 5, 6)]
    assert census[0]["subcubic_graphs"] == 64
    assert census[-1]["cubic_graphs"] == 70
    controls = []
    for n in (4, 5, 6):
        edges = [(i, i + 1) for i in range(n - 1)]
        first, second = (0, 1), (n - 2, n - 1)
        actual = coverage(edges, first, second)
        expected = {4: (False, False), 5: (True, False), 6: (True, True)}[n]
        assert actual == expected
        controls.append({"path_vertices": n, "edge_cover": actual[0],
                         "incident_pair_cover": actual[1]})
    return {"implication": "separated closed neighborhoods imply full local coverage",
            "census": census, "totals": counts, "negative_controls": controls,
            "full_ambient_row_controls": [long_row(seed) for seed in range(12)],
            "scope": "structural geometry only; no colourings enumerated"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", help="compare with a previously recorded JSON receipt")
    args = parser.parse_args()
    result = run()
    if args.verify:
        with open(args.verify, encoding="utf-8") as stream:
            assert json.load(stream) == result
    print(json.dumps(result, indent=2, sort_keys=True))
