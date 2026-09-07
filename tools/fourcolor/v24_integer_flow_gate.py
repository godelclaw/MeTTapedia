#!/usr/bin/env python3
"""Preregistered integral-flow gate for the contour linkage construction.

Exhaust all directed loop-free unit-capacity networks on 2--4 vertices,
with source 0 and sink n-1. Check skew symmetry, every capacity constraint,
conservation, and agreement with independently exhausted cut capacities.
Also require a six-vertex control to cancel flow on a reverse residual arc.
Decompose the final flow into simple positive-flow routes, checking that
subtracting each route preserves feasibility and lowers the value by one.
Outcomes: feasibility_failure, cut_failure, reverse_control_failure, passed.
This is generic flow theory, not a graph-colouring certificate campaign.
"""

import argparse
import itertools
import json
from collections import Counter, deque


def decompose(capacity, original):
    flow = [row[:] for row in original]
    n, routes = len(flow), []
    while sum(flow[0]) > 0:
        parent, queue = {0: None}, deque([0])
        while queue:
            u = queue.popleft()
            for v in range(n):
                if v not in parent and flow[u][v] > 0:
                    parent[v] = u
                    queue.append(v)
        assert n - 1 in parent, "positive_route_failure"
        before, v, route = sum(flow[0]), n - 1, [n - 1]
        while parent[v] is not None:
            u = parent[v]
            flow[u][v] -= 1
            flow[v][u] += 1
            route.append(u)
            v = u
        routes.append(list(reversed(route)))
        assert len(route) == len(set(route)), "positive_route_failure"
        assert sum(flow[0]) == before - 1, "subtraction_failure"
        assert all(flow[u][v] == -flow[v][u] and flow[u][v] <= capacity[u][v]
                   for u in range(n) for v in range(n)), "subtraction_failure"
        assert all(sum(flow[u]) == 0 for u in range(1, n - 1)), "subtraction_failure"
    assert len(routes) == sum(original[0]), "decomposition_failure"
    return routes


def solve(n, edges, capacity=None, exhaustive=True):
    if capacity is None:
        capacity = [[int((u, v) in edges) for v in range(n)] for u in range(n)]
    flow = [[0] * n for _ in range(n)]
    augmentations = []
    reverse_steps = 0
    while True:
        parent, queue = {0: None}, deque([0])
        while queue:
            u = queue.popleft()
            for v in range(n):
                if v not in parent and flow[u][v] < capacity[u][v]:
                    parent[v] = u
                    queue.append(v)
        if n - 1 not in parent:
            break
        v, path = n - 1, [n - 1]
        while parent[v] is not None:
            u = parent[v]
            reverse_steps += capacity[u][v] == 0
            flow[u][v] += 1
            flow[v][u] -= 1
            path.append(u)
            v = u
        augmentations.append(list(reversed(path)))
        assert all(flow[u][v] == -flow[v][u] and flow[u][v] <= capacity[u][v]
                   for u in range(n) for v in range(n)), "feasibility_failure"
        assert all(sum(flow[u]) == 0 for u in range(1, n - 1)), "feasibility_failure"
    reached = set(parent)
    cut = sum(capacity[u][v] for u in reached for v in range(n) if v not in reached)
    assert sum(flow[0]) == cut, "cut_failure"
    if exhaustive:
        all_cuts = []
        for bits in range(1 << (n - 2)):
            S = {0} | {u for u in range(1, n - 1) if bits >> (u - 1) & 1}
            all_cuts.append(sum(capacity[u][v] for u in S for v in range(n) if v not in S))
        assert cut == min(all_cuts), "cut_failure"
    routes = decompose(capacity, flow)
    return dict(value=cut, reverse_steps=reverse_steps, paths=augmentations,
                reached=sorted(reached), flow=flow, decomposition=routes)


def audit():
    counts = Counter()
    for n in range(2, 5):
        pairs = list(itertools.permutations(range(n), 2))
        for bits in range(1 << len(pairs)):
            edges = {e for i, e in enumerate(pairs) if bits >> i & 1}
            result = solve(n, edges)
            counts[f"networks_{n}"] += 1
            counts["augmentations"] += len(result["paths"])
            counts[f"value_{result['value']}"] += 1
    edges = {(0, 1), (0, 2), (1, 3), (1, 4), (2, 3), (3, 5), (4, 5)}
    control = solve(6, edges)
    assert control["value"] == 2 and control["reverse_steps"] > 0, "reverse_control_failure"
    assert [counts[f"networks_{n}"] for n in range(2, 5)] == [4, 64, 4096]
    return dict(schema="fourcolor-v24-integer-flow-v1", counts=dict(counts),
                reverse_control=dict(edges=sorted(edges), **control), outcome="passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only")
    args = parser.parse_args()
    result = json.loads(json.dumps(audit()))
    if args.verify_only:
        with open(args.verify_only) as stream:
            assert json.load(stream) == result, "receipt_mismatch"
        print("fixed integral-flow population replay passed")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
