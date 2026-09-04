#!/usr/bin/env python3
"""Falsification gate for the bounded-face geodesic transfer.

The checked locality theorem retains a bounded four-face window and its
radius-one neighbours.  A physical Count splice needs more: the cumulative
piece between two cuts must have a bounded *complete* interface to the rest
of the graph.  This audit measures both quantities on deterministic diameter
geodesics in the Goldberg GP(k,0) family.

Pre-registered outcomes:

* ``invalid_control``: the source's (5,0) tube does not retain its known
  constant-width radial interfaces, so the audit is not calibrated;
* ``local_to_global_gate_survives``: the tested cumulative geodesic bands
  remain within the same fixed bound as the local carriers;
* ``second_direction_required_on_test_family``: local carriers remain
  bounded but cumulative bands grow past that bound.

The last outcome refutes only the direct inference from radius-one locality
to a complete one-dimensional interface.  It does not refute a
target-dependent construction or a two-directional transfer.
"""

from __future__ import annotations

import argparse
from collections import deque
from pathlib import Path
from typing import Any

from v24_annular_census import atomic_write_json
from v24_goldberg import cap_distances, edge_face_adjacency, make_goldberg_graph
from v24_tube_seed_census import make_tube_annulus
from v24_tube_transfer_audit import distances_from_inner, frontier_edges


SCHEMA = "fourcolor-v24-geodesic-transfer-gate-v1"
LOCAL_CARRIER_BOUND = 30
TUBE_FRONTIER_BOUND = 10


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-frequency", type=int, default=12)
    parser.add_argument("--max-tube-length", type=int, default=20)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_geodesic_transfer_gate.json"),
    )
    return parser.parse_args()


def face_dual_adjacency(graph: dict[str, Any]) -> list[list[int]]:
    adjacency = [set() for _ in graph["face_cycles"]]
    for incident_faces in edge_face_adjacency(graph).values():
        left, right = incident_faces
        adjacency[left].add(right)
        adjacency[right].add(left)
    return [sorted(neighbours) for neighbours in adjacency]


def bfs(
    adjacency: list[list[int]], start: int
) -> tuple[list[int], list[int]]:
    distance = [-1] * len(adjacency)
    parent = [-1] * len(adjacency)
    distance[start] = 0
    queue = deque([start])
    while queue:
        vertex = queue.popleft()
        for neighbour in adjacency[vertex]:
            if distance[neighbour] == -1:
                distance[neighbour] = distance[vertex] + 1
                parent[neighbour] = vertex
                queue.append(neighbour)
    if any(value < 0 for value in distance):
        raise AssertionError("the facial dual is disconnected")
    return distance, parent


def deterministic_diameter_path(adjacency: list[list[int]]) -> list[int]:
    """Choose the lexicographically first ordered diameter pair and a BFS path."""
    best_distance = -1
    best_start = -1
    best_finish = -1
    best_parent: list[int] | None = None
    for start in range(len(adjacency)):
        distance, parent = bfs(adjacency, start)
        finish = min(
            vertex
            for vertex, value in enumerate(distance)
            if value == max(distance)
        )
        candidate = (distance[finish], -start, -finish)
        incumbent = (best_distance, -best_start, -best_finish)
        if candidate > incumbent:
            best_distance = distance[finish]
            best_start = start
            best_finish = finish
            best_parent = parent
    if best_parent is None:
        raise AssertionError("no diameter path was selected")
    path = []
    cursor = best_finish
    while cursor != -1:
        path.append(cursor)
        cursor = best_parent[cursor]
    path.reverse()
    if path[0] != best_start or len(path) != best_distance + 1:
        raise AssertionError("the recovered path is not the selected geodesic")
    return path


def edge_boundary_size(
    adjacency: list[list[int]], vertices: set[int]
) -> int:
    """Dual cut size, hence the primal edge boundary of the face union."""
    return sum(
        neighbour not in vertices
        for vertex in vertices
        for neighbour in adjacency[vertex]
    )


def radius_one(
    adjacency: list[list[int]], vertices: set[int]
) -> set[int]:
    return vertices | {
        neighbour
        for vertex in vertices
        for neighbour in adjacency[vertex]
    }


def audit_tube(length: int) -> dict[str, Any]:
    instance = make_tube_annulus(length)
    distances = distances_from_inner(instance)
    edges = [tuple(edge) for edge in instance["tangle_edges"]]
    widths = [
        len(frontier_edges(edges, distances, level))
        for level in range(max(distances))
    ]
    return {
        "length": length,
        "primal_vertex_count": len(instance["dual_triangles"]),
        "maximum_distance": max(distances),
        "frontier_widths": widths,
        "maximum_frontier_width": max(widths, default=0),
    }


def audit_goldberg(frequency: int) -> dict[str, Any]:
    graph = make_goldberg_graph(frequency)
    adjacency = face_dual_adjacency(graph)
    path = deterministic_diameter_path(adjacency)

    local_rows = []
    for cut in range(len(path) - 1):
        indices = {
            index
            for index in (cut - 1, cut, cut + 1, cut + 2)
            if 0 <= index < len(path)
        }
        window = {path[index] for index in indices}
        carrier = radius_one(adjacency, window)
        local_rows.append(
            {
                "cut": cut,
                "carrier_face_count": len(carrier),
                "carrier_frontier_width": edge_boundary_size(adjacency, carrier),
            }
        )

    prefix_rows = []
    for length in range(1, len(path) + 1):
        axis = set(path[:length])
        band = radius_one(adjacency, axis)
        prefix_rows.append(
            {
                "axis_face_count": length,
                "axis_frontier_width": edge_boundary_size(adjacency, axis),
                "radius_one_band_face_count": len(band),
                "radius_one_band_frontier_width": edge_boundary_size(
                    adjacency, band
                ),
            }
        )

    cap_face = graph["pentagon_face_ids"][0]
    radial_distances = cap_distances(graph, cap_face)
    primal_edges = [tuple(edge) for edge in graph["primal_edges"]]
    radial_widths = [
        sum(
            (radial_distances[left] <= radius)
            != (radial_distances[right] <= radius)
            for left, right in primal_edges
        )
        for radius in range(max(radial_distances))
    ]

    if graph["primal_vertex_count"] != 20 * frequency * frequency:
        raise AssertionError("the Goldberg vertex calibration failed")
    if max(radial_widths, default=0) != 10 * frequency:
        raise AssertionError("the Goldberg radial-frontier calibration failed")

    return {
        "frequency": frequency,
        "primal_vertex_count": graph["primal_vertex_count"],
        "face_count": len(graph["face_cycles"]),
        "graph_hash": graph["graph_hash"],
        "diameter_geodesic": path,
        "diameter": len(path) - 1,
        "local_cut_carriers": local_rows,
        "maximum_local_carrier_face_count": max(
            row["carrier_face_count"] for row in local_rows
        ),
        "maximum_local_carrier_frontier_width": max(
            row["carrier_frontier_width"] for row in local_rows
        ),
        "prefixes": prefix_rows,
        "maximum_axis_prefix_frontier_width": max(
            row["axis_frontier_width"] for row in prefix_rows
        ),
        "maximum_radius_one_prefix_frontier_width": max(
            row["radius_one_band_frontier_width"] for row in prefix_rows
        ),
        "complete_axis_frontier_width": prefix_rows[-1][
            "axis_frontier_width"
        ],
        "complete_radius_one_band_frontier_width": prefix_rows[-1][
            "radius_one_band_frontier_width"
        ],
        "maximum_cap_radial_frontier_width": max(radial_widths, default=0),
    }


def run(max_frequency: int, max_tube_length: int) -> dict[str, Any]:
    if max_frequency < 1 or max_tube_length < 1:
        raise ValueError("both sweep bounds must be positive")
    tube_rows = [audit_tube(length) for length in range(1, max_tube_length + 1)]
    goldberg_rows = [
        audit_goldberg(frequency) for frequency in range(1, max_frequency + 1)
    ]

    tube_control_passed = all(
        row["maximum_frontier_width"] <= TUBE_FRONTIER_BOUND
        for row in tube_rows
    )
    local_bound_passed = all(
        row["maximum_local_carrier_frontier_width"] <= LOCAL_CARRIER_BOUND
        for row in goldberg_rows
    )
    cumulative_exceeds_local = any(
        row["maximum_radius_one_prefix_frontier_width"] > LOCAL_CARRIER_BOUND
        for row in goldberg_rows
    )
    if not tube_control_passed:
        verdict = "invalid_control"
    elif local_bound_passed and cumulative_exceeds_local:
        verdict = "second_direction_required_on_test_family"
    else:
        verdict = "local_to_global_gate_survives"

    return {
        "schema": SCHEMA,
        "algorithm": "diameter-geodesic-radius-one-prefix-frontier-v1",
        "pre_registered_bounds": {
            "tube_frontier": TUBE_FRONTIER_BOUND,
            "local_carrier_frontier": LOCAL_CARRIER_BOUND,
        },
        "verdict": verdict,
        "tube_control_passed": tube_control_passed,
        "goldberg_local_bound_passed": local_bound_passed,
        "goldberg_cumulative_exceeds_local_bound": cumulative_exceeds_local,
        "tube_controls": tube_rows,
        "goldberg_rows": goldberg_rows,
        "scope_warning": (
            "This refutes only the inference from the checked radius-one "
            "locality lemma to a bounded complete one-dimensional interface. "
            "It does not refute a target-forced or two-directional transfer."
        ),
    }


def main() -> int:
    args = parse_args()
    result = run(args.max_frequency, args.max_tube_length)
    atomic_write_json(args.output, result)
    print(
        "tube_control:",
        max(row["maximum_frontier_width"] for row in result["tube_controls"]),
    )
    for row in result["goldberg_rows"]:
        print(
            f"k={row['frequency']:2d} "
            f"diameter={row['diameter']:2d} "
            f"local={row['maximum_local_carrier_frontier_width']:3d} "
            f"cumulative={row['maximum_radius_one_prefix_frontier_width']:3d}"
        )
    print("verdict=", result["verdict"])
    print("certificate=", args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
