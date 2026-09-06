#!/usr/bin/env python3
"""Optimize complete interfaces, rather than measuring a chosen sweep.

For a facial-dual diameter geodesic, source terminals are all vertices on its
prefix faces; sink terminals are all vertices on its suffix faces, leaving
one intervening face unconstrained. Every off-axis vertex may be reassigned.
In a cubic map, faces at dual distance >= 2 cannot share a vertex, so these
terminal sets are disjoint. Each terminal set contains a cycle.

Pre-registered outcomes: invalid_control if source tubes exceed width 10;
optimized_width_exceeds_local_bound if a certified optimum exceeds 30;
otherwise optimized_width_within_test_bound. A separate cap-only experiment
checks whether permitting all future axis vertices to move destroys progress.
No result claims a target counterexample or an optimum branchwidth bound.

Each minimum cut is certified independently by equally many undirected
edge-disjoint terminal-to-terminal paths. The exact boundary is also traced
as a simple cycle in the supplied spherical dual. No colouring is enumerated.
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter, deque
from pathlib import Path

from v24_annular_census import atomic_write_json, induced_cycle_order
from v24_geodesic_transfer_gate import deterministic_diameter_path, face_dual_adjacency
from v24_goldberg import consistently_oriented_face_cycles, edge_face_adjacency, make_goldberg_graph
from v24_tube_seed_census import make_tube_annulus


def reach(adj: list[dict[int, int]], start: int) -> tuple[set[int], dict[int, int]]:
    parent = {start: start}
    queue = deque([start])
    while queue:
        u = queue.popleft()
        for v, capacity in adj[u].items():
            if capacity > 0 and v not in parent:
                parent[v] = u
                queue.append(v)
    return set(parent), parent


def minimum_cut(n: int, edges: list[tuple[int, int]], source: set[int], sink: set[int]):
    assert source and sink and source.isdisjoint(sink)
    s, t = n, n + 1
    residual = [{} for _ in range(n + 2)]
    for u, v in edges:
        residual[u][v] = residual[v][u] = 1
    large = len(edges) + 1
    for u in sorted(source):
        residual[s][u], residual[u][s] = large, 0
    for u in sorted(sink):
        residual[u][t], residual[t][u] = large, 0
    initial = [dict(row) for row in residual]
    while True:
        seen, parent = reach(residual, s)
        if t not in seen:
            break
        path = [t]
        while path[-1] != s:
            path.append(parent[path[-1]])
        path.reverse()
        amount = min(residual[u][v] for u, v in zip(path, path[1:]))
        for u, v in zip(path, path[1:]):
            residual[u][v] -= amount
            residual[v][u] += amount
    side = seen - {s}
    positive = [{v: max(0, capacity - residual[u][v]) for v, capacity in row.items()}
                for u, row in enumerate(initial)]
    paths = []
    while True:
        found, parent = reach(positive, s)
        if t not in found:
            break
        path = [t]
        while path[-1] != s:
            path.append(parent[path[-1]])
        path.reverse()
        for u, v in zip(path, path[1:]):
            positive[u][v] -= 1
        paths.append(path[1:-1])
    return side, paths


def connected(n: int, edges: list[tuple[int, int]], side: set[int]) -> bool:
    if not side:
        return False
    adjacency = [{} for _ in range(n)]
    for u, v in edges:
        if u in side and v in side:
            adjacency[u][v] = adjacency[v][u] = 1
    return reach(adjacency, min(side))[0] == side


def verify_certificate(n, edges, source, sink, side, paths):
    """Path packing gives a lower bound; the displayed cut gives the upper bound."""
    edge_set = {tuple(sorted(e)) for e in edges}
    assert source <= side and sink.isdisjoint(side)
    assert connected(n, edges, source) and connected(n, edges, sink)
    assert connected(n, edges, side) and connected(n, edges, set(range(n)) - side)
    cut = [i for i, (u, v) in enumerate(edges) if (u in side) != (v in side)]
    used = set()
    for path in paths:
        assert path[0] in source and path[-1] in sink and len(set(path)) == len(path)
        assert any((u in side) != (v in side) for u, v in zip(path, path[1:]))
        for u, v in zip(path, path[1:]):
            e = tuple(sorted((u, v)))
            assert e in edge_set and e not in used
            used.add(e)
    assert len(cut) == len(paths)
    return cut


def boundary_order(edge_faces, cut):
    adjacency = {}
    for e in cut:
        u, v = edge_faces[e]
        adjacency.setdefault(u, []).append((e, v))
        adjacency.setdefault(v, []).append((e, u))
    assert adjacency and all(len(row) == 2 for row in adjacency.values())
    start = min(adjacency)
    current, last = start, -1
    order, faces = [], []
    while True:
        faces.append(current)
        e, nxt = min(pair for pair in adjacency[current] if pair[0] != last)
        order.append(e)
        current, last = nxt, e
        if current == start:
            break
        assert current not in faces
    assert set(order) == set(cut) and len(order) == len(cut)
    return order, faces


def validate_sphere(graph):
    edges = [tuple(e) for e in graph["primal_edges"]]
    n = graph["primal_vertex_count"]
    assert all(sum(v in e for e in edges) == 3 for v in range(n))
    faces = consistently_oriented_face_cycles(graph)
    assert n - len(edges) + len(faces) == 2
    darts = Counter()
    rotation = {}
    for face in faces:
        assert len(face) == len(set(face))
        for i, v in enumerate(face):
            u, w = face[i - 1], face[(i + 1) % len(face)]
            darts[u, v] += 1
            rotation[v, u] = (v, w)
    assert darts == Counter({(u, v): 1 for a, b in edges for u, v in [(a, b), (b, a)]})
    for d in rotation:
        assert rotation[d] != d and rotation[rotation[d]] != d
        assert rotation[rotation[rotation[d]]] == d


def closed_tube(length):
    tube = make_tube_annulus(length)
    edges = tube["primal_edges"]
    n = len(tube["dual_triangles"])
    neighbors = [[] for _ in range(n)]
    for u, v in edges:
        neighbors[u].append(v)
        neighbors[v].append(u)
    faces = [induced_cycle_order({i for i, tri in enumerate(tube["dual_triangles"]) if f in tri}, neighbors)
             for f in range(tube["dual_vertex_count"])]
    return {"primal_edges": edges, "primal_vertex_count": n, "face_cycles": faces}


def audit(graph, name):
    validate_sphere(graph)
    edges = [tuple(e) for e in graph["primal_edges"]]
    n = graph["primal_vertex_count"]
    path = deterministic_diameter_path(face_dual_adjacency(graph))
    face_vertices = [set(graph["face_cycles"][f]) for f in path]
    edge_faces = edge_face_adjacency(graph)
    rows = []
    sides = []
    for i in range(len(path) - 2):
        source = set.union(*face_vertices[:i + 1])
        sink = set.union(*face_vertices[i + 2:])
        side, paths = minimum_cut(n, edges, source, sink)
        cut = verify_certificate(n, edges, source, sink, side, paths)
        order, face_order = boundary_order(edge_faces, cut)
        if sides:
            assert sides[-1] <= side
        if len(sides) >= 2:
            assert sides[-2] < side
        sides.append(side)
        rows.append({"axis_split": i, "source": sorted(source), "sink": sorted(sink),
                     "minimum_width": len(cut), "side": sorted(side),
                     "boundary_edge_order": order, "boundary_face_order": face_order,
                     "edge_disjoint_paths": paths})
    cap_sink = face_vertices[-1]
    relaxed_sides, relaxed_widths = [], []
    for i in range(len(path) - 2):
        source = set.union(*face_vertices[:i + 1])
        side, paths = minimum_cut(n, edges, source, cap_sink)
        cap_cut = verify_certificate(n, edges, source, cap_sink, side, paths)
        boundary_order(edge_faces, cap_cut)
        if relaxed_sides:
            assert relaxed_sides[-1] <= side
        relaxed_sides.append(side)
        relaxed_widths.append(len(cap_cut))
    worst = max(rows, key=lambda row: row["minimum_width"])
    result = {"name": name, "vertices": n, "face_geodesic": path,
              "maximum_minimum_width": worst["minimum_width"],
              "minimum_widths": [row["minimum_width"] for row in rows],
              "distinct_nested_sides": len({tuple(sorted(s)) for s in sides}),
              "cap_relaxed_widths": relaxed_widths,
              "cap_relaxed_distinct_sides": len({tuple(sorted(s)) for s in relaxed_sides}),
              "worst_cut_certificate": worst}
    print({k: v for k, v in result.items()
           if k not in {"worst_cut_certificate", "face_geodesic", "minimum_widths", "cap_relaxed_widths"}}, flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-frequency", type=int, default=12)
    parser.add_argument("--max-tube-length", type=int, default=12)
    parser.add_argument("--output", type=Path, default=Path("results/fourcolor/v24_geodesic_mincut_gate.json"))
    parser.add_argument("--verify-only", type=Path, help="Verify saved worst-cut witnesses without running flow optimization")
    args = parser.parse_args()
    if args.verify_only:
        verify_archive(json.loads(args.verify_only.read_text()))
        return
    small = audit_uncrossing_small()
    tubes = [audit(closed_tube(j), f"tube({j})") for j in range(1, args.max_tube_length + 1)]
    spheres = [audit(make_goldberg_graph(k), f"GP({k},0)") for k in range(1, args.max_frequency + 1)]
    verdict = ("invalid_control" if any(row["maximum_minimum_width"] > 10 for row in tubes)
               else "optimized_width_exceeds_local_bound" if any(row["maximum_minimum_width"] > 30 for row in spheres)
               else "optimized_width_within_test_bound")
    atomic_write_json(args.output, {"schema": "fourcolor-geodesic-mincut-gate-v1", "verdict": verdict,
                                    "exhaustive_uncrossing": small,
                                    "tube_controls": tubes, "goldberg_controls": spheres})
    print(verdict)


def verify_archive(data):
    """Reconstruct each map and check packing/cut witnesses, with no flow solver."""
    checked = 0
    for family, rows in [("tube", data["tube_controls"]), ("goldberg", data["goldberg_controls"])]:
        for row in rows:
            parameter = int(row["name"].split("(")[1].split(",")[0].rstrip(")"))
            graph = closed_tube(parameter) if family == "tube" else make_goldberg_graph(parameter)
            validate_sphere(graph)
            edges = [tuple(e) for e in graph["primal_edges"]]
            n = graph["primal_vertex_count"]
            assert n == row["vertices"]
            axis = row["face_geodesic"]
            adjacency = face_dual_adjacency(graph)
            assert all(b in adjacency[a] for a, b in zip(axis, axis[1:]))
            from v24_geodesic_transfer_gate import bfs
            assert bfs(adjacency, axis[0])[0][axis[-1]] == len(axis) - 1
            cert = row["worst_cut_certificate"]
            i = cert["axis_split"]
            faces = graph["face_cycles"]
            source = set.union(*(set(faces[f]) for f in axis[:i + 1]))
            sink = set.union(*(set(faces[f]) for f in axis[i + 2:]))
            assert source == set(cert["source"]) and sink == set(cert["sink"])
            side = set(cert["side"])
            cut = verify_certificate(n, edges, source, sink, side, cert["edge_disjoint_paths"])
            assert len(cut) == cert["minimum_width"] == row["maximum_minimum_width"]
            order, face_order = boundary_order(edge_face_adjacency(graph), cut)
            assert order == cert["boundary_edge_order"] and face_order == cert["boundary_face_order"]
            # Deliberately duplicate a packed path: the checker must reject it.
            try:
                verify_certificate(n, edges, source, sink, side,
                                   cert["edge_disjoint_paths"] + [cert["edge_disjoint_paths"][0]])
            except AssertionError:
                pass
            else:
                raise AssertionError("duplicate-path negative control was accepted")
            checked += 1
    print({"saved_optimum_certificates_verified_without_solver": checked,
           "duplicate_path_mutations_rejected": checked})


def audit_uncrossing_small():
    """Gate before the generic proof: canonical cuts nest as terminals advance.

    Test every graph through four vertices, every admissible terminal pair,
    and every monotone transition (including a vertex moving sink to source).
    No connectedness assumption is needed for this uncrossing claim.
    """
    rows = []
    transitions = [(0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2)]
    for n in range(5):
        possible = list(itertools.combinations(range(n), 2))
        checked = solver_checks = 0
        for graphmask in range(1 << len(possible)):
            edges = [e for i, e in enumerate(possible) if graphmask >> i & 1]
            width = [sum((s >> u & 1) != (s >> v & 1) for u, v in edges) for s in range(1 << n)]
            canonical = {}
            for labels in itertools.product(range(3), repeat=n):
                a = sum(1 << v for v in range(n) if labels[v] == 0)
                b = sum(1 << v for v in range(n) if labels[v] == 2)
                feasible = [s for s in range(1 << n) if s & a == a and not s & b]
                best = min(feasible, key=lambda s: (width[s], s.bit_count(), s))
                assert all(best & s == best for s in feasible if width[s] == width[best])
                canonical[labels] = best
                source = {v for v in range(n) if a >> v & 1}
                sink = {v for v in range(n) if b >> v & 1}
                if (connected(n, edges, set(range(n))) and connected(n, edges, source)
                        and connected(n, edges, sink)):
                    side, paths = minimum_cut(n, edges, source, sink)
                    verify_certificate(n, edges, source, sink, side, paths)
                    assert sum(1 << v for v in side) == best
                    solver_checks += 1
            for choices in itertools.product(transitions, repeat=n):
                old = canonical[tuple(c[0] for c in choices)]
                new = canonical[tuple(c[1] for c in choices)]
                assert old & new == old
                checked += 1
        rows.append({"vertices": n, "graphs": 1 << len(possible),
                     "terminal_transitions": checked, "solver_checks": solver_checks})
    print({"exhaustive_uncrossing": rows}, flush=True)
    return rows


if __name__ == "__main__":
    main()
