#!/usr/bin/env python3
"""Preregistered marked-material gate for complete cotree cut chains.

Prediction: (t+1)*n+1 nested sides contain n consecutive slabs acquiring
none of t marked vertices. Test all small arrival schedules and full cuts
of the existing spherical controls, including shore connectivity, cycles,
boundary return order and width. A prism control tests the stronger, NOT
predicted implication that avoiding marked endpoints also avoids cutting
a frozen edge. Outcomes: window_failure, interface_failure, passed.
No colouring enumeration or zero-Count example is used.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_contour_mesh_gate import verify_archive
from v24_geodesic_mincut_gate import boundary_order, connected, validate_sphere
from v24_goldberg import consistently_oriented_face_cycles, edge_face_adjacency
from v24_thin_annulus_cut_gate import annulus
from v24_tree_cotree_gate import bfs_tree, inspect, return_permutation


def window(sides, marks, n):
    assert len(sides) >= (len(marks) + 1) * n + 1
    for j in range(len(marks) + 1):
        lo, hi = j * n, (j + 1) * n
        if sides[lo] & marks == sides[hi] & marks:
            assert not ((sides[hi] - sides[lo]) & marks), "window_failure"
            assert all(sides[i] & marks == sides[lo] & marks
                       for i in range(lo, hi + 1)), "window_failure"
            return lo, hi
    raise AssertionError("window_failure")


def schedules():
    tested = 0
    for t in range(5):
        for n in range(1, 5):
            N = (t + 1) * n + 1
            for arrival in itertools.product(range(N + 1), repeat=t):
                # An arrival at N stays outside throughout the sequence.
                counts = [sum(a <= i for a in arrival) for i in range(N)]
                assert any(counts[j * n] == counts[(j + 1) * n]
                           for j in range(t + 1)), "window_failure"
                tested += 1
    # Sharpness for n slabs: with t transitions, every constant run can
    # have only n entries, totaling (t+1)*n cuts without n clean slabs.
    sharp = []
    for t, n in itertools.product(range(5), range(1, 5)):
        values = [i // n for i in range((t + 1) * n)]
        assert not any(values[i] == values[i + n]
                       for i in range(len(values) - n))
        sharp.append(dict(marks=t, slabs=n, cuts=len(values)))
    return dict(arrival_schedules=tested, sharpness_controls=sharp)


def graph_cases(graph):
    checked = inspect(graph)  # Full original-edge, cyclic-order regression.
    edges = [tuple(e) for e in graph["primal_edges"]]
    N, ef = graph["primal_vertex_count"], edge_face_adjacency(graph)
    F = len(graph["face_cycles"])
    _, depth, de, _ = bfs_tree(F, ef, 0)
    primal = {e: uv for e, uv in enumerate(edges) if e not in set(de.values())}
    parent, pd, _, order = bfs_tree(N, primal, 0)
    side = {v: {v} for v in order}
    for v in reversed(order[1:]):
        side[parent[v]] |= side[v]
    tip = max(order, key=lambda v: pd[v])
    chain = []
    while parent[tip] != tip:
        S = side[tip]
        inner = sum(u in S and v in S for u, v in edges)
        outer = sum(u not in S and v not in S for u, v in edges)
        if inner >= len(S) and outer >= N - len(S):
            chain.append(S)
        tip = parent[tip]
    marked_cases, material_cases = [], []
    for marks in (set(), {0}, {0, N - 1}, {0, N // 2, N - 1}):
        n = (len(chain) - 1) // (len(marks) + 1)
        if n < 1:
            continue
        lo, hi = window(chain, marks, n)
        for A, B in zip(chain[lo:hi], chain[lo + 1:hi + 1]):
            assert A < B and not ((B - A) & marks), "window_failure"
        marked_cases.append(dict(marks=sorted(marks), slabs=n, start=lo, end=hi))
    width = 2 * max(depth.values()) + 1
    stride = 6 * width + 1
    edge_shores = [{e for e, (u, v) in enumerate(edges) if u in S or v in S}
                   for S in chain]
    incident = [{e for e, uv in enumerate(edges) if v in uv} for v in range(N)]
    majority = [{v for v in range(N) if len(incident[v] & A) >= 2}
                for A in edge_shores]
    spaced = majority[::stride]
    for marks in (set(), {0}, {0, N - 1}):
        n = (len(spaced) - 1) // (len(marks) + 1)
        if n < 1:
            continue
        lo, hi = window(spaced, marks, n)
        for i in range(lo, hi):
            A, B = edge_shores[stride * i], edge_shores[stride * (i + 1)]
            stars = {v for v in range(N) if incident[v] <= B - A}
            assert stars and stars.isdisjoint(marks), "interface_failure"
            assert spaced[i] < spaced[i + 1], "interface_failure"
        material_cases.append(dict(marks=sorted(marks), slabs=n, start=lo,
                                   end=hi, stride=stride))
    return dict(vertices=N, dual_height=max(depth.values()), cyclic_cuts=len(chain),
                full_cut_checks=checked["cut_checks"], marked_cases=marked_cases,
                material_cases=material_cases)


def frozen_edge_control():
    # Octagonal prism, with four nested cyclic full cuts through the same
    # frozen edge. Its endpoints are outside every intervening slab.
    k = 8
    edges = [(i, (i + 1) % k) for i in range(k)]
    edges += [(k + i, k + (i + 1) % k) for i in range(k)]
    edges += [(i, k + i) for i in range(k)]
    edges = [tuple(sorted(e)) for e in edges]
    faces = [list(range(k)), list(range(k, 2 * k))]
    faces += [[i, (i + 1) % k, k + (i + 1) % k, k + i] for i in range(k)]
    graph = dict(primal_vertex_count=16, primal_edges=[list(e) for e in edges],
                 face_cycles=faces)
    validate_sphere(graph)
    ef = edge_face_adjacency(graph)
    oriented = consistently_oriented_face_cycles(graph)
    sides = [set(range(j)) | set(range(k, k + j)) for j in range(2, 6)]
    marks = {0, 7}
    for S in sides:
        other = set(range(16)) - S
        assert connected(16, edges, S) and connected(16, edges, other)
        assert sum(u in S and v in S for u, v in edges) >= len(S)
        assert sum(u in other and v in other for u, v in edges) >= len(other)
        assert sum((u in S) != (v in S) for u, v in edges) == 4
        assert (0 in S) != (7 in S)
        cut = {e for e, (u, v) in enumerate(edges) if (u in S) != (v in S)}
        boundary_order(ef, sorted(cut))
        left = return_permutation(oriented, S, cut, edges)
        right = return_permutation(oriented, other, cut, edges)
        assert all(right[left[e]] == e for e in cut)
        shore = {e for e, (u, v) in enumerate(edges) if u in S or v in S}
        assert {v for v in range(16)
                if sum(v in edges[e] for e in shore) >= 2} == S
    assert not ((sides[-1] - sides[0]) & marks)
    return dict(vertices=16, frozen_edge=[0, 7], prefix_rungs=[2, 3, 4, 5],
                full_width=4, endpoints_avoided=True, frozen_edge_crossed=True,
                majority_sides_equal=True, opposite_returns_inverse=True, graph=graph)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-only", type=Path)
    args = parser.parse_args()
    archive = json.loads(Path("results/fourcolor/v24_contour_mesh_gate.json").read_text())
    verify_archive(archive)
    population = [dict(family=f"GP({r['frequency']},0)", **graph_cases(r["graph"]))
                  for r in archive["receipts"]]
    population += [dict(family=f"annulus({k},{L})", **graph_cases(annulus(k, L)[0]))
                   for L in range(1, 5) for k in (8, 16, 32, 64)]
    population.append(dict(family="annulus(256,1)", **graph_cases(annulus(256, 1)[0])))
    assert any(c["marks"] for row in population for c in row["material_cases"])
    result = dict(schema="fourcolor-v24-marked-cotree-v1", schedules=schedules(),
                  population=population, frozen_edge_control=frozen_edge_control(),
                  outcome="passed")
    assert result == json.loads(json.dumps(result)), "noncanonical_receipt"
    if args.output:
        atomic_write_json(args.output, result)
    if args.verify_only:
        assert result == json.loads(args.verify_only.read_text()), "receipt_mismatch"
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
