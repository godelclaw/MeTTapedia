#!/usr/bin/env python3
"""Audit v24 Goldberg specimens against the cyclic-cut normal-form criterion."""

from __future__ import annotations

import argparse
from collections import Counter, deque
from pathlib import Path
from typing import Any

from v24_annular_census import atomic_write_json
from v24_goldberg import face_edge_indices, make_goldberg_graph


SCHEMA = "fourcolor-v24-goldberg-normal-form-audit-v1"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Check Goldberg graphs against the v24 normal form."
    )
    parser.add_argument("--frequencies", type=int, nargs="+", default=[3, 8])
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_normal_form_audit.json"),
    )
    return parser.parse_args()


def adjacency_from_edges(
    vertex_count: int, edges: list[tuple[int, int]]
) -> list[set[int]]:
    adjacency = [set() for _ in range(vertex_count)]
    for left, right in edges:
        adjacency[left].add(right)
        adjacency[right].add(left)
    return adjacency


def dual_adjacency(graph: dict[str, Any]) -> list[set[int]]:
    edges = {
        tuple(sorted((left, right)))
        for triangle in graph["dual_triangles"]
        for left, right in (
            (triangle[0], triangle[1]),
            (triangle[0], triangle[2]),
            (triangle[1], triangle[2]),
        )
    }
    return adjacency_from_edges(graph["dual_vertex_count"], sorted(edges))


def canonical_cycle(cycle: tuple[int, ...]) -> tuple[int, ...]:
    rotations = []
    for oriented in (cycle, tuple(reversed(cycle))):
        rotations.extend(
            oriented[index:] + oriented[:index] for index in range(len(cycle))
        )
    return min(rotations)


def cycles_of_length(
    adjacency: list[set[int]], length: int
) -> set[tuple[int, ...]]:
    cycles: set[tuple[int, ...]] = set()
    for start in range(len(adjacency)):
        path = [start]

        def search(vertex: int) -> None:
            if len(path) == length:
                if start in adjacency[vertex]:
                    cycles.add(canonical_cycle(tuple(path)))
                return
            for neighbor in adjacency[vertex]:
                if neighbor < start or neighbor in path:
                    continue
                path.append(neighbor)
                search(neighbor)
                path.pop()

        search(start)
    return cycles


def connected_after_removal(
    adjacency: list[set[int]], removed: frozenset[int]
) -> bool:
    remaining = [
        vertex for vertex in range(len(adjacency)) if vertex not in removed
    ]
    if not remaining:
        return True
    visited = {remaining[0]}
    queue = deque([remaining[0]])
    while queue:
        vertex = queue.popleft()
        for neighbor in adjacency[vertex]:
            if neighbor not in removed and neighbor not in visited:
                visited.add(neighbor)
                queue.append(neighbor)
    return len(visited) == len(remaining)


def is_connected(adjacency: list[set[int]]) -> bool:
    return connected_after_removal(adjacency, frozenset())


def bridge_count(adjacency: list[set[int]]) -> int:
    discovery = [-1] * len(adjacency)
    low = [-1] * len(adjacency)
    time = 0
    bridges = 0

    def search(vertex: int, parent: int) -> None:
        nonlocal time, bridges
        discovery[vertex] = low[vertex] = time
        time += 1
        for neighbor in adjacency[vertex]:
            if neighbor == parent:
                continue
            if discovery[neighbor] == -1:
                search(neighbor, vertex)
                low[vertex] = min(low[vertex], low[neighbor])
                if low[neighbor] > discovery[vertex]:
                    bridges += 1
            else:
                low[vertex] = min(low[vertex], discovery[neighbor])

    for vertex in range(len(adjacency)):
        if discovery[vertex] == -1:
            search(vertex, -1)
    return bridges


def graph_distances(
    adjacency: list[set[int]], sources: set[int]
) -> list[int]:
    distances = [-1] * len(adjacency)
    queue = deque(sorted(sources))
    for source in queue:
        distances[source] = 0
    while queue:
        vertex = queue.popleft()
        for neighbor in adjacency[vertex]:
            if distances[neighbor] == -1:
                distances[neighbor] = distances[vertex] + 1
                queue.append(neighbor)
    return distances


def audit_frequency(frequency: int) -> dict[str, Any]:
    graph = make_goldberg_graph(frequency)
    primal_edges = [tuple(edge) for edge in graph["primal_edges"]]
    primal_adjacency = adjacency_from_edges(
        graph["primal_vertex_count"], primal_edges
    )
    triangulation_adjacency = dual_adjacency(graph)
    facial_triangles = {
        canonical_cycle(tuple(triangle)) for triangle in graph["dual_triangles"]
    }
    three_cycles = cycles_of_length(triangulation_adjacency, 3)
    four_cycles = cycles_of_length(triangulation_adjacency, 4)
    separating_four_cycles = [
        cycle
        for cycle in four_cycles
        if not connected_after_removal(
            triangulation_adjacency, frozenset(cycle)
        )
    ]

    primal_five_cycles = cycles_of_length(primal_adjacency, 5)
    facial_pentagons = {
        canonical_cycle(tuple(cycle))
        for cycle in graph["face_cycles"]
        if len(cycle) == 5
    }
    face_edges = face_edge_indices(graph)
    face_size_histogram = Counter(map(len, graph["face_cycles"]))
    face_incidence = Counter(
        edge for boundary in face_edges for edge in boundary
    )

    pentagon_vertices = {
        vertex
        for face in graph["pentagon_face_ids"]
        for vertex in graph["face_cycles"][face]
    }
    hexagon_pentagon_distances = []
    for face, cycle in enumerate(graph["face_cycles"]):
        if len(cycle) != 6:
            continue
        distances = graph_distances(primal_adjacency, set(cycle))
        hexagon_pentagon_distances.append(
            min(distances[vertex] for vertex in pentagon_vertices)
        )

    nonfacial_triangles = three_cycles - facial_triangles
    criterion_holds = (
        min(map(len, triangulation_adjacency)) >= 5
        and not nonfacial_triangles
        and not separating_four_cycles
    )
    return {
        "frequency": frequency,
        "graph_hash": graph["graph_hash"],
        "primal_vertex_count": graph["primal_vertex_count"],
        "primal_edge_count": len(primal_edges),
        "face_count": len(graph["face_cycles"]),
        "face_size_histogram": {
            str(size): count
            for size, count in sorted(face_size_histogram.items())
        },
        "all_face_curvature_sum": sum(
            6 - len(cycle) for cycle in graph["face_cycles"]
        ),
        "euler_characteristic": (
            graph["primal_vertex_count"]
            - len(primal_edges)
            + len(graph["face_cycles"])
        ),
        "primal_degree_histogram": {
            str(degree): count
            for degree, count in sorted(
                Counter(map(len, primal_adjacency)).items()
            )
        },
        "primal_connected": is_connected(primal_adjacency),
        "primal_bridge_count": bridge_count(primal_adjacency),
        "every_primal_edge_has_two_incident_faces": all(
            face_incidence[edge] == 2 for edge in range(len(primal_edges))
        ),
        "dual_vertex_count": len(triangulation_adjacency),
        "dual_degree_histogram": {
            str(degree): count
            for degree, count in sorted(
                Counter(map(len, triangulation_adjacency)).items()
            )
        },
        "dual_three_cycle_count": len(three_cycles),
        "dual_facial_triangle_count": len(facial_triangles),
        "dual_nonfacial_three_cycle_count": len(nonfacial_triangles),
        "dual_four_cycle_count": len(four_cycles),
        "dual_separating_four_cycle_count": len(separating_four_cycles),
        "primal_five_cycle_count": len(primal_five_cycles),
        "facial_pentagon_count": len(facial_pentagons),
        "every_primal_five_cycle_is_a_facial_pentagon": (
            primal_five_cycles == facial_pentagons
        ),
        "pentagon_far_hexagon_count": sum(
            distance >= 2 for distance in hexagon_pentagon_distances
        ),
        "maximum_hexagon_pentagon_distance": max(
            hexagon_pentagon_distances, default=0
        ),
        "dual_normal_form_cycle_criterion_holds": criterion_holds,
    }


def main() -> int:
    args = parse_args()
    if any(frequency < 1 for frequency in args.frequencies):
        raise SystemExit("Goldberg frequencies must be positive")
    rows = [audit_frequency(frequency) for frequency in args.frequencies]
    if not all(row["dual_normal_form_cycle_criterion_holds"] for row in rows):
        raise AssertionError("a Goldberg specimen fails the dual normal form")
    if not all(row["all_face_curvature_sum"] == 12 for row in rows):
        raise AssertionError("a spherical cubic specimen has the wrong curvature")
    result = {
        "schema": SCHEMA,
        "algorithm": "explicit-cycle-and-separation-enumeration-v1",
        "criterion": (
            "minimum dual degree five, no nonfacial dual triangle, "
            "and no separating dual four-cycle"
        ),
        "graphs": rows,
    }
    atomic_write_json(args.output, result)
    print(
        "; ".join(
            f"GP({row['frequency']},0): normal form, "
            f"{row['primal_five_cycle_count']} facial 5-cycles"
            for row in rows
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
