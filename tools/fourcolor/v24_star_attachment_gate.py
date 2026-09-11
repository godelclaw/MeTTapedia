#!/usr/bin/env python3
"""Preregistered component gate for the compositional vertex constructor.

Attach one new vertex to an arbitrary list of old vertices. The predicted
component quotient is the untouched old components plus one merged component,
and C_new + touched = C_old + 1. Consumed ports need not be in distinct
components or at distinct vertices. No planar or connected-prefix assumption
is used. Exhaust all simple graphs of order at most four and attachment lists
of length at most three; independently reconstruct zero-cut port observations.
This is an evaluator control, not a configuration or colouring catalogue.
"""

from itertools import combinations, product
import json

from v24_topology_viability_gate import component_labels


def check(n, edges, ports):
    old = component_labels(n, edges)
    touched = {old[p] for p in ports}
    new = component_labels(n + 1, edges + tuple((p, n) for p in ports))
    predicted = tuple(None if c in touched else c for c in old) + (None,)
    for a, b in product(range(n + 1), repeat=2):
        assert (new[a] == new[b]) == (predicted[a] == predicted[b])
    assert len(set(new)) + len(touched) == len(set(old)) + 1
    zero_cuts = [mask for mask in range(1 << n)
                 if all(((mask >> a) & 1) == ((mask >> b) & 1) for a, b in edges)]
    columns = {tuple((mask >> p) & 1 for mask in zero_cuts) for p in ports}
    assert len(columns) == len(touched)
    for p, q in product(ports, repeat=2):
        observed = all(((mask >> p) & 1) == ((mask >> q) & 1) for mask in zero_cuts)
        assert observed == (old[p] == old[q])
    return len(set(new)), len(touched), len(set(old))


def run():
    checked = empty_seams = repeated_vertices = multi_component = 0
    for n in range(5):
        options = tuple(combinations(range(n), 2))
        for mask in range(1 << len(options)):
            edges = tuple(e for i, e in enumerate(options) if (mask >> i) & 1)
            for h in range(4):
                for ports in product(range(n), repeat=h):
                    _, touched, _ = check(n, edges, ports)
                    checked += 1
                    empty_seams += not ports
                    repeated_vertices += len(set(ports)) < h
                    multi_component += touched > 1
    # Three ports in one component consume three edges but merge only one
    # old component into the new vertex. Counting ports as components fails.
    control = check(3, ((0, 1), (1, 2)), (0, 1, 2))
    assert control == (1, 1, 1)
    assert control[0] + 3 != control[2] + 1
    return dict(checked=checked, empty_seams=empty_seams,
                repeated_vertices=repeated_vertices, multi_component=multi_component,
                ports_are_not_components_control=control)


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
