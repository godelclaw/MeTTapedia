#!/usr/bin/env python3
"""Complete primal frontiers of connected facial bipartitions.

Preregistered populations: all nonempty proper face sets of the dodecahedral
sphere (12 faces) and the 3 by 3 periodic honeycomb torus (9 faces). Retain
exactly the sets whose two induced facial sides are connected. Test their
ENTIRE primal edge boundary, not a selected component of that boundary.

Outcomes: invalid_rotation; sphere_frontier_failure; or sphere_passed, with
the torus recording whether dropping sphericity permits multiple cycles.
No colouring, minimal-counterexample assumption, width bound, or catalogue
of reducible configurations is involved. Replay reconstructs the two maps
and exhausts the same fixed populations; it uses no optimization solver.
"""

from __future__ import annotations

import argparse
import copy
import json
from collections import Counter
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_contour_mesh_gate import component, cycle_order
from v24_geodesic_transfer_gate import face_dual_adjacency
from v24_goldberg import (consistently_oriented_face_cycles,
                          edge_face_adjacency, make_goldberg_graph)


SCHEMA = "fourcolor-v24-facial-bond-v1"


def torus():
    def vertex(i, j, s):
        return 2 * ((i % 3) * 3 + j % 3) + s

    rotation = {}
    for i in range(3):
        for j in range(3):
            a, b = vertex(i, j, 0), vertex(i, j, 1)
            rotation[a] = [b, vertex(i - 1, j, 1), vertex(i, j - 1, 1)]
            rotation[b] = [a, vertex(i + 1, j, 0), vertex(i, j + 1, 0)]
    seen, faces = set(), []
    for u in sorted(rotation):
        for v in rotation[u]:
            if (u, v) in seen:
                continue
            dart, face = (u, v), []
            while dart not in seen:
                seen.add(dart)
                a, b = dart
                face.append(a)
                dart = b, rotation[b][(rotation[b].index(a) + 1) % 3]
            assert dart == (u, v), "invalid_rotation"
            faces.append(face)
    return {"primal_vertex_count": 18,
            "primal_edges": sorted({tuple(sorted((u, v)))
                                    for u, ns in rotation.items() for v in ns}),
            "face_cycles": faces}


def validate(graph, euler):
    n, edges = graph["primal_vertex_count"], graph["primal_edges"]
    edge_set = {tuple(sorted(e)) for e in edges}
    assert len(edge_set) == len(edges) and all(0 <= u < v < n for u, v in edge_set)
    assert Counter(v for e in edges for v in e) == Counter({v: 3 for v in range(n)})
    primal = [[] for _ in range(n)]
    for u, v in edges:
        primal[u].append(v)
        primal[v].append(u)
    assert component(primal, set(range(n)), 0) == set(range(n))
    faces = consistently_oriented_face_cycles(graph)
    assert n - len(edges) + len(faces) == euler
    darts, rho = Counter(), {}
    for face in faces:
        assert len(face) >= 3 and len(face) == len(set(face))
        for i, v in enumerate(face):
            u, w = face[i - 1], face[(i + 1) % len(face)]
            darts[u, v] += 1
            assert (v, u) not in rho
            rho[v, u] = v, w
    assert darts == Counter({d: 1 for u, v in edges for d in ((u, v), (v, u))})
    assert all(rho[d] != d and rho[rho[d]] != d and rho[rho[rho[d]]] == d for d in rho)
    dual = face_dual_adjacency(graph)
    assert component(dual, set(range(len(faces))), 0) == set(range(len(faces)))


def audit(graph, euler):
    validate(graph, euler)
    edges, dual = graph["primal_edges"], face_dual_adjacency(graph)
    sides = edge_face_adjacency(graph)
    full = set(range(len(dual)))
    histogram, accepted, first_multiple = Counter(), 0, None
    for mask in range(1, (1 << len(dual)) - 1):
        selected = {f for f in full if (mask >> f) & 1}
        complement = full - selected
        if (component(dual, selected, min(selected)) != selected or
                component(dual, complement, min(complement)) != complement):
            continue
        accepted += 1
        boundary = {e for e, (f, g) in sides.items() if (f in selected) != (g in selected)}
        assert boundary
        neighbors = [[] for _ in range(graph["primal_vertex_count"])]
        for e in boundary:
            u, v = edges[e]
            neighbors[u].append(v)
            neighbors[v].append(u)
        vertices = {v for v, ns in enumerate(neighbors) if ns}
        assert all(len(neighbors[v]) == 2 for v in vertices)
        cycles, unused = [], set(boundary)
        while unused:
            root = edges[min(unused)][0]
            reached = component(neighbors, vertices, root)
            part = {e for e in unused if edges[e][0] in reached}
            cycles.append(cycle_order(edges, part))
            unused -= part
        histogram[len(cycles)] += 1
        if euler == 2:
            assert len(cycles) == 1, "sphere_frontier_failure"
        elif len(cycles) > 1 and first_multiple is None:
            first_multiple = {"selected_faces": sorted(selected),
                              "boundary_edges": sorted(boundary), "cycles": cycles}
    return {"vertices": graph["primal_vertex_count"], "edges": len(edges),
            "faces": len(dual), "euler": euler,
            "proper_face_sets": (1 << len(dual)) - 2,
            "both_sides_connected": accepted,
            "boundary_components": {str(k): v for k, v in sorted(histogram.items())},
            "first_multiple": first_multiple}


def receipt():
    sphere = make_goldberg_graph(1)
    toroidal = torus()
    result = {"schema": SCHEMA, "sphere": audit(sphere, 2),
              "torus_graph": toroidal, "torus": audit(toroidal, 0)}
    assert result["torus"]["first_multiple"] is not None
    return result


def verify(saved):
    # Normalize tuple-valued edge lists to the JSON representation.
    assert saved == json.loads(json.dumps(receipt())), "receipt_mismatch"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", type=Path)
    parser.add_argument("--output", type=Path,
                        default=Path("results/fourcolor/v24_facial_bond_gate.json"))
    args = parser.parse_args()
    if args.verify_only:
        verify(json.loads(args.verify_only.read_text()))
        print("replay: fixed complete populations verified")
        return
    result = json.loads(json.dumps(receipt()))
    verify(result)
    bad = copy.deepcopy(result)
    bad["torus"]["first_multiple"]["cycles"].pop()
    try:
        verify(bad)
    except AssertionError:
        pass
    else:
        raise AssertionError("missing boundary component was accepted")
    atomic_write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ("sphere", "torus")}, indent=2))
    print("missing-component corruption rejected")


if __name__ == "__main__":
    main()
