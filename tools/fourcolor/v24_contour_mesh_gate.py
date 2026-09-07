#!/usr/bin/env python3
"""Extract the stack's injective mesh from full ambient contour/linkage data.

Pre-registered population: spherical cubic GP(k,0), k=1..8, all faces 5/6.
For root face 0 choose the first farthest face. At depth i, retain the
component of faces at distance >i containing that far face; take its entire
primal edge boundary. Select the middle half of these contours (rounded
outward), and compute vertex-disjoint paths between the two extreme cycles
in the FULL ambient graph, with terminal vertices also of capacity one.

Outcomes: invalid_control for failed spherical/cubic data; contour_failure
for noncyclic or overlapping boundaries; linkage_failure if a packed path
misses a selected contour; otherwise mesh_constructed. No growth formula,
optimal branchwidth, zero Count, or global wall theorem is presumed.

The receipt retains all edges/faces, contour regions, paths, a matching-size
vertex separator, and distinct row-column branch vertices. Replay does not
run a flow solver. These are geometric witnesses, not colouring certificates.
"""

from __future__ import annotations

import argparse
import copy
import json
from collections import deque
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_geodesic_mincut_gate import connected, reach, validate_sphere
from v24_geodesic_transfer_gate import bfs, face_dual_adjacency
from v24_goldberg import edge_face_adjacency, make_goldberg_graph


SCHEMA = "fourcolor-v24-contour-mesh-v1"
POPULATION = list(range(1, 9))


def component(adjacency, allowed, root):
    assert root in allowed
    seen, queue = {root}, deque([root])
    while queue:
        for v in adjacency[queue.popleft()]:
            if v in allowed and v not in seen:
                seen.add(v)
                queue.append(v)
    return seen


def cycle_order(edges, selected):
    adjacency = {}
    for e in selected:
        u, v = edges[e]
        adjacency.setdefault(u, []).append(v)
        adjacency.setdefault(v, []).append(u)
    assert adjacency and all(len(vs) == 2 for vs in adjacency.values()), "contour_failure"
    start, previous = min(adjacency), None
    order, current = [], start
    while True:
        assert current not in order, "contour_failure"
        order.append(current)
        nxt = min(v for v in adjacency[current] if v != previous)
        previous, current = current, nxt
        if current == start:
            break
    assert len(order) == len(selected), "contour_failure"
    return order


def linkage(n, edges, source, sink):
    """Unit vertex capacities, including endpoints; retain all ambient edges."""
    assert source and sink and source.isdisjoint(sink)
    s, t = 2 * n, 2 * n + 1
    residual = [{} for _ in range(2 * n + 2)]

    def arc(u, v, cap):
        residual[u][v] = cap
        residual[v].setdefault(u, 0)

    for u in range(n):
        arc(2 * u, 2 * u + 1, 1)
    for u, v in edges:
        arc(2 * u + 1, 2 * v, n + 1)
        arc(2 * v + 1, 2 * u, n + 1)
    for u in sorted(source):
        arc(s, 2 * u, n + 1)
    for u in sorted(sink):
        arc(2 * u + 1, t, n + 1)
    initial = [dict(row) for row in residual]
    while True:
        seen, parent = reach(residual, s)
        if t not in seen:
            break
        v = t
        while v != s:
            u = parent[v]
            residual[u][v] -= 1
            residual[v][u] += 1
            v = u
    separator = [u for u in range(n) if 2 * u in seen and 2 * u + 1 not in seen]
    positive = [{v: max(0, cap - residual[u][v]) for v, cap in row.items()}
                for u, row in enumerate(initial)]
    paths = []
    while True:
        found, parent = reach(positive, s)
        if t not in found:
            break
        walk, v = [t], t
        while v != s:
            u = parent[v]
            positive[u][v] -= 1
            walk.append(u)
            v = u
        paths.append([v // 2 for v in reversed(walk[1:-1]) if v % 2 == 0])
    return paths, separator


def extract(k):
    raw = make_goldberg_graph(k)
    graph = {key: raw[key] for key in ("primal_vertex_count", "primal_edges", "face_cycles")}
    validate_sphere(graph)
    dual = face_dual_adjacency(graph)
    dist, _ = bfs(dual, 0)
    far = dist.index(max(dist))
    edges, edge_faces = graph["primal_edges"], edge_face_adjacency(graph)
    contours = []
    for i in range(max(dist)):
        deep = component(dual, {f for f, d in enumerate(dist) if d > i}, far)
        boundary = [e for e, (f, g) in edge_faces.items() if (f in deep) != (g in deep)]
        contours.append({"depth": i, "faces": sorted(deep),
                         "cycle": cycle_order(edges, boundary)})
    first, last = len(contours) // 4, len(contours) - len(contours) // 4 - 1
    assert first < last
    rows = contours[first:last + 1]
    paths, separator = linkage(graph["primal_vertex_count"], edges,
                               set(rows[0]["cycle"]), set(rows[-1]["cycle"]))
    branches = [[next(v for v in path if v in row["cycle"]) for path in paths] for row in rows]
    return {"frequency": k, "graph": graph, "root": 0, "far": far,
            "contours": contours, "selected": [first, last], "paths": paths,
            "separator": separator, "branches": branches}


def verify(receipt):
    graph = receipt["graph"]
    validate_sphere(graph)
    n, edges = graph["primal_vertex_count"], graph["primal_edges"]
    k = receipt["frequency"]
    assert n == 20 * k * k and len(edges) == 30 * k * k
    assert all(len(face) in (5, 6) for face in graph["face_cycles"])
    assert sum(len(face) == 5 for face in graph["face_cycles"]) == 12
    assert connected(n, edges, set(range(n)))
    edge_ids = {tuple(sorted(edge)): e for e, edge in enumerate(edges)}
    edge_faces = edge_face_adjacency(graph)
    dual = face_dual_adjacency(graph)
    distance, _ = bfs(dual, receipt["root"])
    far = receipt["far"]
    assert receipt["root"] == 0 and far == distance.index(max(distance))
    contours = receipt["contours"]
    assert len(contours) == max(distance) and contours
    incident = [set() for _ in range(n)]
    for f, face in enumerate(graph["face_cycles"]):
        for v in face:
            incident[v].add(f)
    # The local hypothesis used in the generic distance-layer proof: the
    # incident faces of a cubic vertex form a clique in the facial dual.
    assert all(f == h or h in dual[f] for fs in incident for f in fs for h in fs)
    used, regions = set(), []
    for i, row in enumerate(contours):
        deep, cycle = set(row["faces"]), row["cycle"]
        assert row["depth"] == i
        assert len(deep) == len(row["faces"])
        assert deep == component(dual, {f for f, d in enumerate(distance) if d > i}, far)
        other = set(range(len(dual))) - deep
        assert component(dual, other, receipt["root"]) == other
        if regions:
            assert deep < regions[-1]
        regions.append(deep)
        assert len(cycle) >= 3 and len(cycle) == len(set(cycle))
        assert set(cycle).isdisjoint(used), "contour_failure"
        used.update(cycle)
        actual = {e for e, (f, g) in edge_faces.items() if (f in deep) != (g in deep)}
        displayed = [edge_ids[tuple(sorted((u, v)))] for u, v in zip(cycle, cycle[1:] + cycle[:1])]
        assert len(displayed) == len(actual) and set(displayed) == actual
        assert all(min(distance[f] for f in incident[v]) == i for v in cycle)
        # Entire vertex frontier, not merely those points visited by the linkage.
        inner = {v for v in range(n) if incident[v] <= deep}
        frontier = {v for v in range(n) if incident[v] & deep and incident[v] - deep}
        assert frontier == set(cycle)
        assert all(v in inner or v in frontier for u, v in edges if u in inner)
        assert all(u in inner or u in frontier for u, v in edges if v in inner)
    first, last = receipt["selected"]
    assert [first, last] == [len(contours) // 4, len(contours) - len(contours) // 4 - 1]
    assert first < last
    rows = contours[first:last + 1]
    source, sink = set(rows[0]["cycle"]), set(rows[-1]["cycle"])
    paths, separator = receipt["paths"], set(receipt["separator"])
    assert paths and len(paths) == len(separator) == len(receipt["separator"])
    assert separator <= set(range(n))
    used = set()
    for path in paths:
        assert path and path[0] in source and path[-1] in sink
        assert len(path) == len(set(path)) and set(path).isdisjoint(used)
        used.update(path)
        assert all(tuple(sorted(edge)) in edge_ids for edge in zip(path, path[1:]))
        assert all(set(path) & set(row["cycle"]) for row in rows), "linkage_failure"
    # Matching-size separator certifies optimality of THIS terminal linkage.
    adjacency = [[] for _ in range(n)]
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    allowed, seen = set(range(n)) - separator, set()
    for root in sorted(source - separator):
        if root not in seen:
            seen |= component(adjacency, allowed, root)
    assert seen.isdisjoint(sink - separator)
    branches = receipt["branches"]
    assert len(branches) == len(rows)
    assert all(len(row) == len(paths) for row in branches)
    all_branches = [v for row in branches for v in row]
    assert len(set(all_branches)) == len(rows) * len(paths)
    for i, row in enumerate(branches):
        for j, vertex in enumerate(row):
            assert vertex in rows[i]["cycle"] and vertex in paths[j]
    return {"frequency": k, "vertices": n, "contours": len(contours),
            "rows": len(rows), "columns": len(paths), "branches": len(all_branches)}


def verify_archive(archive):
    assert archive["schema"] == SCHEMA
    assert [r["frequency"] for r in archive["receipts"]] == POPULATION
    summaries = [verify(row) for row in archive["receipts"]]
    assert summaries == archive["summary"]
    return summaries


def negative_checks(receipts):
    rejected = 0
    for row in receipts:
        for kind in ("column", "contour", "branch"):
            bad = copy.deepcopy(row)
            if kind == "column":
                bad["paths"][1] = bad["paths"][0]
            elif kind == "contour":
                bad["contours"][0]["cycle"].pop()
            else:
                bad["branches"][0][1] = bad["branches"][0][0]
            try:
                verify(bad)
            except (AssertionError, KeyError):
                rejected += 1
            else:
                raise AssertionError("corrupted mesh receipt accepted")
    assert rejected == 3 * len(receipts)
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", type=Path)
    parser.add_argument("--output", type=Path,
                        default=Path("results/fourcolor/v24_contour_mesh_gate.json"))
    args = parser.parse_args()
    if args.verify_only:
        archive = json.loads(args.verify_only.read_text())
    else:
        receipts = [extract(k) for k in POPULATION]
        archive = {"schema": SCHEMA, "receipts": receipts,
                   "summary": [verify(row) for row in receipts]}
    for row in verify_archive(archive):
        print(json.dumps(row), flush=True)
    print("corruptions rejected:", negative_checks(archive["receipts"]), flush=True)
    if not args.verify_only:
        atomic_write_json(args.output, archive)


if __name__ == "__main__":
    main()
