#!/usr/bin/env python3
"""Endpoint gate for composite two-vertex deletion moves.

Pre-registered: on uncolourable controls with colourable pair-deletion
exteriors, find a monochromatic four-port word and colour all three
loop-free reconnections. Temporary intermediate graphs are irrelevant to
this endpoint test. Controls include nonplanar bridgeless graphs; they
are not planar least-counterexample specimens or a patch catalogue.
"""

from collections import Counter
import json

import networkx as nx

from v24_absolute_topology_gate import control_graph, enumerated
from v24_deletion_orbit_gate import incidence


PAIRINGS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))


def deletion_control(n, edges, site):
    u, v = site
    graph = nx.Graph(edges)
    ports = sorted(set(graph[u]) - {v}) + sorted(set(graph[v]) - {u})
    assert len(set(ports)) == 4
    kept = sorted(set(range(n)) - {u, v})
    index = {old: new for new, old in enumerate(kept)}
    core = sorted(tuple(sorted((index[a], index[b]))) for a, b in edges
                  if a in index and b in index)
    slots = [index[p] for p in ports]
    inc = incidence(n-2, core)
    colors = enumerated(n-2, core)
    assert colors, "exterior-colourability premise is absent"
    words = []
    for c in colors:
        w = tuple(next(iter(set(range(3)) - {c[e] for e in inc[p]})) for p in slots)
        assert w[0] == w[1] and w[2] == w[3]
        words.append(w)
    mono = [i for i, w in enumerate(words) if len(set(w)) == 1]
    assert mono, "monochromatic seam claim refuted"
    counts = Counter(words)
    assert len(counts) == 9 and len(set(counts.values())) == 1
    completions = []
    for pairing in PAIRINGS:
        added = [tuple(sorted((slots[a], slots[b]))) for a, b in pairing]
        target = sorted(core + added)
        assert len(set(target)) == len(target)
        assert all(a != b for a, b in target)
        assert all(len(star) == 3 for star in incidence(n-2, target))
        cols = enumerated(n-2, target)
        assert cols, "a zero-Count smaller endpoint exists"
        source = colors[mono[0]]
        candidate = {edge: source[i] for i, edge in enumerate(core)}
        candidate.update({edge: words[mono[0]][0] for edge in added})
        assert bytes(candidate[e] for e in target) in cols
        completions.append(len(cols))
    return dict(site=list(site), exterior_count=len(colors),
                monochromatic_count=len(mono), completion_counts=completions)


def gate():
    petersen = sorted(tuple(sorted(e)) for e in nx.petersen_graph().edges())
    nflower, flower = control_graph()
    results = {}
    for name, n, edges in (("petersen", 10, petersen), ("flower5", nflower, flower)):
        g = nx.Graph(edges)
        assert all(d == 3 for _, d in g.degree())
        assert nx.is_connected(g) and not list(nx.bridges(g))
        assert not nx.check_planarity(g)[0]
        assert not enumerated(n, edges)
        cases = [deletion_control(n, edges, site) for site in edges]
        results[name] = dict(vertices=n, edges=[list(e) for e in edges],
                             planar=False, bridgeless=True, cases=cases)
    return dict(controls=results,
                scope="Nonplanar controls: not a refutation of the planar compositional route.",
                endpoint_cases=sum(len(r["cases"]) for r in results.values()))


if __name__ == "__main__":
    print(json.dumps(gate(), indent=2, sort_keys=True))
