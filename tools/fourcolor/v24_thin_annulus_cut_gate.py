#!/usr/bin/env python3
"""Full-face cuts versus actual narrow decompositions of thin annuli.

Pre-registered gate: at thickness two, all displayed caterpillar tree cuts
must have middle-set size <= 12. A cap-separating cut has optimum exactly
the circumference, certified by disjoint complete rungs. Circumference 32
therefore tests whether small branchwidth controls this forced full-face cut
within the earlier local budget 30. Failure of sphere/cut/decomposition
validation is an invalid control, not evidence about the route.

These are generic spherical cubic controls, with long faces and girth >= 5.
They are not zero-Count counterexamples. No wall-exclusion or grid-to-mesh
conversion is asserted. No colouring or reducibility certificate is generated.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, deque
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_geodesic_mincut_gate import boundary_order, connected, validate_sphere, verify_certificate
from v24_geodesic_transfer_gate import bfs, deterministic_diameter_path, face_dual_adjacency
from v24_goldberg import edge_face_adjacency


def annulus(circumference: int, thickness: int):
    assert circumference >= 5 and thickness >= 1
    k, L = circumference, thickness
    height = 2 * L + 2

    def vertex(row, column):
        return (column % k) * height + row

    edges, order = [], []

    def add(u, v):
        order.append(len(edges))
        edges.append(tuple(sorted((u, v))))

    for i in range(k):
        for r in range(height - 1):
            add(vertex(r, i), vertex(r + 1, i))
        add(vertex(0, i), vertex(0, i + 1))
        for j in range(1, L + 1):
            add(vertex(2 * j, i), vertex(2 * j - 1, i + 1))
        add(vertex(height - 1, i), vertex(height - 1, i + 1))
    assert len(set(edges)) == len(edges)
    faces = [[vertex(0, i) for i in range(k)],
             [vertex(height - 1, i) for i in range(k)]]
    # Ordered layers of pentagons/hexagons between the two cap faces.
    for i in range(k):
        faces.append([vertex(0, i), vertex(0, i + 1), vertex(1, i + 1),
                      vertex(2, i), vertex(1, i)])
    for j in range(1, L):
        for i in range(k):
            faces.append([vertex(2 * j, i), vertex(2 * j + 1, i), vertex(2 * j + 2, i),
                          vertex(2 * j + 1, i + 1), vertex(2 * j, i + 1),
                          vertex(2 * j - 1, i + 1)])
    for i in range(k):
        faces.append([vertex(height - 1, i), vertex(2 * L, i), vertex(2 * L - 1, i + 1),
                      vertex(2 * L, i + 1), vertex(height - 1, i + 1)])
    graph = {"primal_vertex_count": k * height, "primal_edges": edges, "face_cycles": faces}
    axis = [0] + [2 + j * k for j in range(L + 1)] + [1]
    paths = [[vertex(r, i) for r in range(height)] for i in range(k)]
    return graph, order, axis, paths


def girth(n, edges):
    adjacency = [[] for _ in range(n)]
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    answer = n + 1
    for root in range(n):
        distance, parent = {root: 0}, {root: -1}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in adjacency[u]:
                if v not in distance:
                    distance[v], parent[v] = distance[u] + 1, u
                    queue.append(v)
                elif parent[u] != v:
                    answer = min(answer, distance[u] + distance[v] + 1)
    return answer


def verify_caterpillar(n, edges, order):
    """Root = first leaf, left = second, right = right-comb of remaining leaves.

    Internal comb shores are suffixes. Checking every prefix (symmetric
    middle sets) and every singleton thus checks every edge of this concrete
    branch-decomposition tree, not just a chosen vertex frontier.
    """
    assert len(order) >= 3 and sorted(order) == list(range(len(edges)))
    total = Counter(v for edge in edges for v in edge)
    seen, widths = Counter(), []
    disconnected_prefixes, disconnected_suffixes = [], []
    for i, eid in enumerate(order[:-1]):
        seen.update(edges[eid])
        middle = sorted(v for v in seen if 0 < seen[v] < total[v])
        widths.append(len(middle))
        before = [edges[e] for e in order[:i + 1]]
        after = [edges[e] for e in order[i + 1:]]
        # A raw branch decomposition does not require connected shores. Record
        # this separately; the cap cut itself must have two connected shores.
        if not connected(n, before, {v for edge in before for v in edge}):
            disconnected_prefixes.append(i + 1)
        if not connected(n, after, {v for edge in after for v in edge}):
            disconnected_suffixes.append(i + 1)
    leaf_widths = [sum(total[v] > 1 for v in edge) for edge in edges]
    return {"tree": "root-first-left-second-right-comb-rest",
            "leaf_order": order, "maximum_middle_size": max(widths + leaf_widths),
            "worst_prefix_length": 1 + max(range(len(widths)), key=widths.__getitem__),
            "disconnected_prefix_lengths": disconnected_prefixes,
            "disconnected_suffix_lengths": disconnected_suffixes}


def perimeter_chain(graph, k, L):
    """Check the complete boundaries of intervals of 2,...,k-2 rungs.

    This is a diagnostic alternative on this family, not a supplier for the
    target class. Both cross-cuts are retained, including both cap edges.
    """
    n, edges = graph["primal_vertex_count"], graph["primal_edges"]
    height, rows, previous, previous_edges = 2 * L + 2, [], set(), set()
    degree = Counter(v for edge in edges for v in edge)
    for count in range(2, k - 1):
        side = set(range(count * height))
        complement = set(range(n)) - side
        inside = {i for i, (u, v) in enumerate(edges) if u in side and v in side}
        outside = {i for i, (u, v) in enumerate(edges) if u in complement and v in complement}
        assert connected(n, edges, side) and connected(n, edges, complement)
        assert len(inside) >= len(side) and len(outside) >= len(complement)
        inner_degree = Counter(v for e in inside for v in edges[e])
        outer_degree = Counter(v for e in outside for v in edges[e])
        assert all(2 <= inner_degree[v] <= degree[v] for v in side)
        assert all(2 <= outer_degree[v] <= degree[v] for v in complement)
        if rows:
            assert previous < side and previous_edges < inside
        cut = [i for i, (u, v) in enumerate(edges) if (u in side) != (v in side)]
        assert len(cut) == 2 * L + 4
        order, faces = boundary_order(edge_face_adjacency(graph), cut)
        rows.append({"rungs": count, "side_vertices": len(side),
                     "cut_edge_order": order, "cut_face_order": faces})
        previous, previous_edges = side, inside
    return {"width": 2 * L + 4, "strictly_nested_sides": len(rows), "cuts": rows}


def make_receipt(k, L):
    graph, order, axis, paths = annulus(k, L)
    n, edges, faces = graph["primal_vertex_count"], graph["primal_edges"], graph["face_cycles"]
    validate_sphere(graph)
    assert connected(n, edges, set(range(n)))
    assert girth(n, edges) >= 5
    dual = face_dual_adjacency(graph)
    assert bfs(dual, 0)[0][1] == len(axis) - 1
    assert all(b in dual[a] for a, b in zip(axis, axis[1:]))
    source = set(faces[0])
    sink = set.union(*(set(faces[f]) for f in axis[2:]))
    # The cap itself is feasible even with the full future face union forced out.
    cut = verify_certificate(n, edges, source, sink, source, paths)
    assert len(cut) == k
    edge_order, face_order = boundary_order(edge_face_adjacency(graph), cut)
    decomposition = verify_caterpillar(n, edges, order)
    if L == 2:
        assert decomposition["maximum_middle_size"] <= 12, "invalid narrow control"
    return {"circumference": k, "thickness": L, "vertices": n,
            "face_length_histogram": dict(Counter(map(len, faces))),
            "girth": girth(n, edges), "cap_geodesic": axis,
            "dual_diameter": len(deterministic_diameter_path(dual)) - 1,
            "source": sorted(source), "sink": sorted(sink), "side": sorted(source),
            "cut_edge_order": edge_order, "cut_face_order": face_order,
            "edge_disjoint_rungs": paths, "optimum_forced_cut_size": k,
            "branch_decomposition": decomposition,
            "perimeter_chain": perimeter_chain(graph, k, L)}


def verify_receipt(row):
    """Rebuild the graph; check supplied witnesses without cut optimization."""
    k, L = row["circumference"], row["thickness"]
    graph, _, _, _ = annulus(k, L)
    n, edges, faces = graph["primal_vertex_count"], graph["primal_edges"], graph["face_cycles"]
    validate_sphere(graph)
    assert n == row["vertices"] and connected(n, edges, set(range(n)))
    assert dict(Counter(map(len, faces))) == {int(k): v for k, v in row["face_length_histogram"].items()}
    assert girth(n, edges) == row["girth"] >= 5
    axis, dual = row["cap_geodesic"], face_dual_adjacency(graph)
    assert axis[0] == 0 and axis[-1] == 1
    assert all(b in dual[a] for a, b in zip(axis, axis[1:]))
    assert bfs(dual, 0)[0][1] == len(axis) - 1
    assert len(deterministic_diameter_path(dual)) - 1 == row["dual_diameter"]
    source = set(faces[axis[0]])
    sink = set.union(*(set(faces[f]) for f in axis[2:]))
    assert source == set(row["source"]) and sink == set(row["sink"])
    cut = verify_certificate(n, edges, source, sink, set(row["side"]), row["edge_disjoint_rungs"])
    assert len(cut) == row["optimum_forced_cut_size"] == k
    boundary = boundary_order(edge_face_adjacency(graph), cut)
    assert boundary == (row["cut_edge_order"], row["cut_face_order"])
    computed = verify_caterpillar(n, edges, row["branch_decomposition"]["leaf_order"])
    assert computed == row["branch_decomposition"]
    assert computed["maximum_middle_size"] <= 12
    assert perimeter_chain(graph, k, L) == row["perimeter_chain"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", type=Path)
    parser.add_argument("--output", type=Path, default=Path("results/fourcolor/v24_thin_annulus_cut_gate.json"))
    args = parser.parse_args()
    if args.verify_only:
        data = json.loads(args.verify_only.read_text())
    else:
        data = {"schema": "fourcolor-thin-annulus-cut-gate-v1", "thickness": 2,
                "controls": [make_receipt(k, 2) for k in (5, 8, 16, 32, 64)]}
    assert data["schema"] == "fourcolor-thin-annulus-cut-gate-v1" and data["thickness"] == 2
    assert [row["circumference"] for row in data["controls"]] == [5, 8, 16, 32, 64]
    assert all(row["thickness"] == 2 for row in data["controls"])
    for row in data["controls"]:
        verify_receipt(row)
        # Reject a missing/repeated decomposition leaf and a duplicated rung.
        for field in ("leaf", "path", "boundary"):
            mutant = json.loads(json.dumps(row))
            if field == "leaf":
                mutant["branch_decomposition"]["leaf_order"][-1] = 0
            elif field == "path":
                mutant["edge_disjoint_rungs"][-1] = mutant["edge_disjoint_rungs"][0]
            else:
                mutant["perimeter_chain"]["cuts"][0]["cut_edge_order"][0] = -1
            try:
                verify_receipt(mutant)
            except AssertionError:
                pass
            else:
                raise AssertionError(f"accepted corrupted {field} witness")
        print({"circumference": row["circumference"], "vertices": row["vertices"],
               "forced_cut_optimum": row["optimum_forced_cut_size"],
               "displayed_branchwidth": row["branch_decomposition"]["maximum_middle_size"],
               "dual_diameter": row["dual_diameter"],
               "width_eight_perimeter_sides": row["perimeter_chain"]["strictly_nested_sides"]}, flush=True)
    if not args.verify_only:
        assert any(row["optimum_forced_cut_size"] > 30 for row in data["controls"])
        data["verdict"] = "forced_full_face_cut_exceeds_budget_despite_narrow_decomposition"
        atomic_write_json(args.output, data)
    print(f"all witnesses verified; {3 * len(data['controls'])} corrupted-witness controls rejected")


if __name__ == "__main__":
    main()
