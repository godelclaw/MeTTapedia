"""Combinatorial Goldberg GP(k,0) fullerenes for v24 certificate checks."""

from __future__ import annotations

from collections import Counter, defaultdict
from typing import Any

from v24_annular_census import canonical_hash, dualize_triangulation, induced_cycle_order


ICOSAHEDRON_FACES = (
    (0, 1, 2),
    (0, 1, 7),
    (0, 2, 6),
    (0, 5, 6),
    (0, 5, 7),
    (1, 2, 8),
    (1, 3, 7),
    (1, 3, 8),
    (2, 4, 6),
    (2, 4, 8),
    (3, 7, 11),
    (3, 8, 9),
    (3, 9, 11),
    (4, 6, 10),
    (4, 8, 9),
    (4, 9, 10),
    (5, 6, 10),
    (5, 7, 11),
    (5, 10, 11),
    (9, 10, 11),
)


def geodesic_triangulation(
    frequency: int,
) -> tuple[list[tuple[int, int, int]], int, list[int]]:
    if frequency < 1:
        raise ValueError("the Goldberg frequency must be positive")
    point_ids: dict[tuple[tuple[int, int], ...], int] = {}
    original_vertices: dict[int, int] = {}

    def point_id(
        left: int, middle: int, right: int, middle_weight: int, right_weight: int
    ) -> int:
        left_weight = frequency - middle_weight - right_weight
        key = tuple(
            sorted(
                (vertex, weight)
                for vertex, weight in (
                    (left, left_weight),
                    (middle, middle_weight),
                    (right, right_weight),
                )
                if weight
            )
        )
        if key not in point_ids:
            point_ids[key] = len(point_ids)
        if len(key) == 1:
            original_vertices[key[0][0]] = point_ids[key]
        return point_ids[key]

    triangles = set()
    for left, middle, right in ICOSAHEDRON_FACES:
        points = {}
        for middle_weight in range(frequency + 1):
            for right_weight in range(frequency + 1 - middle_weight):
                points[(middle_weight, right_weight)] = point_id(
                    left, middle, right, middle_weight, right_weight
                )
        for middle_weight in range(frequency):
            for right_weight in range(frequency - middle_weight):
                triangles.add(
                    tuple(
                        sorted(
                            (
                                points[(middle_weight, right_weight)],
                                points[(middle_weight + 1, right_weight)],
                                points[(middle_weight, right_weight + 1)],
                            )
                        )
                    )
                )
                if middle_weight + right_weight <= frequency - 2:
                    triangles.add(
                        tuple(
                            sorted(
                                (
                                    points[(middle_weight + 1, right_weight)],
                                    points[(middle_weight, right_weight + 1)],
                                    points[(middle_weight + 1, right_weight + 1)],
                                )
                            )
                        )
                    )

    result = sorted(triangles)
    point_count = len(point_ids)
    if point_count != 10 * frequency * frequency + 2:
        raise AssertionError("the geodesic point count is wrong")
    if len(result) != 20 * frequency * frequency:
        raise AssertionError("the geodesic triangle count is wrong")
    if set(original_vertices) != set(range(12)):
        raise AssertionError("the twelve original icosahedron vertices were not retained")
    pentagon_points = sorted(original_vertices.values())
    return result, point_count, pentagon_points


def make_goldberg_graph(frequency: int) -> dict[str, Any]:
    triangles, dual_vertex_count, pentagon_points = geodesic_triangulation(
        frequency
    )
    primal_edges, neighbors = dualize_triangulation(triangles, dual_vertex_count)
    face_cycles = [
        induced_cycle_order(
            {
                index
                for index, triangle in enumerate(triangles)
                if dual_vertex in triangle
            },
            neighbors,
        )
        for dual_vertex in range(dual_vertex_count)
    ]
    certificate_face_cycles = [
        certificate_cycle_order(
            {
                index
                for index, triangle in enumerate(triangles)
                if dual_vertex in triangle
            },
            neighbors,
        )
        for dual_vertex in range(dual_vertex_count)
    ]
    if any(
        set(cycle) != set(certificate_cycle)
        for cycle, certificate_cycle in zip(
            face_cycles, certificate_face_cycles, strict=True
        )
    ):
        raise AssertionError("the two face traversals disagree on incidence")
    face_length_histogram = Counter(map(len, face_cycles))
    if face_length_histogram != Counter({5: 12, 6: dual_vertex_count - 12}):
        raise AssertionError("the dual is not a pentagon-hexagon fullerene")
    pentagon_face_ids = [
        index for index, cycle in enumerate(face_cycles) if len(cycle) == 5
    ]
    if pentagon_face_ids != pentagon_points:
        raise AssertionError("pentagon faces do not match icosahedron vertices")
    graph_payload = {
        "frequency": frequency,
        "dual_vertex_count": dual_vertex_count,
        "dual_triangles": [list(triangle) for triangle in triangles],
        "primal_vertex_count": len(triangles),
        "primal_edges": [list(edge) for edge in primal_edges],
        "face_cycles": face_cycles,
        "pentagon_face_ids": pentagon_face_ids,
    }
    return {
        **graph_payload,
        "graph_hash": canonical_hash(graph_payload),
        "certificate_face_cycles": certificate_face_cycles,
        "neighbors": neighbors,
    }


def certificate_cycle_order(
    face_vertices: set[int], neighbors: list[list[int]]
) -> list[int]:
    """Reproduce the specimen generator's per-face direction convention."""
    face_neighbors = {
        vertex: [
            adjacent
            for adjacent in set(neighbors[vertex])
            if adjacent in face_vertices
        ]
        for vertex in face_vertices
    }
    if any(len(adjacent) != 2 for adjacent in face_neighbors.values()):
        raise AssertionError("a fullerene face is not an induced cycle")

    start = min(face_vertices)
    order = [start]
    previous = None
    current = start
    while True:
        choices = [
            adjacent
            for adjacent in face_neighbors[current]
            if adjacent != previous
        ]
        if not choices:
            raise AssertionError("the certificate face traversal got stuck")
        successor = choices[0]
        if successor == start:
            break
        if successor in order:
            raise AssertionError("the certificate face traversal repeated a vertex")
        order.append(successor)
        previous, current = current, successor
    if set(order) != face_vertices:
        raise AssertionError("the certificate face traversal missed a vertex")
    return order


def face_edge_indices(graph: dict[str, Any]) -> list[list[int]]:
    edge_index = {
        tuple(edge): index for index, edge in enumerate(graph["primal_edges"])
    }
    result = []
    for cycle in graph["face_cycles"]:
        result.append(
            [
                edge_index[
                    tuple(sorted((cycle[index], cycle[(index + 1) % len(cycle)])))
                ]
                for index in range(len(cycle))
            ]
        )
    return result


def cap_distances(graph: dict[str, Any], cap_face_id: int) -> list[int]:
    distances = [-1] * graph["primal_vertex_count"]
    frontier = list(graph["face_cycles"][cap_face_id])
    for vertex in frontier:
        distances[vertex] = 0
    cursor = 0
    while cursor < len(frontier):
        vertex = frontier[cursor]
        cursor += 1
        for neighbor in graph["neighbors"][vertex]:
            if distances[neighbor] == -1:
                distances[neighbor] = distances[vertex] + 1
                frontier.append(neighbor)
    if any(distance < 0 for distance in distances):
        raise AssertionError("the Goldberg graph is disconnected")
    return distances


def make_cap_tangle(graph: dict[str, Any], cap_face_id: int) -> dict[str, Any]:
    cap = graph["face_cycles"][cap_face_id]
    cap_vertices = set(cap)
    primal_edges = [tuple(edge) for edge in graph["primal_edges"]]
    removed_edges = {
        tuple(sorted((cap[index], cap[(index + 1) % len(cap)])))
        for index in range(len(cap))
    }
    tangle_edges = [edge for edge in primal_edges if edge not in removed_edges]
    incidence = [[] for _ in range(graph["primal_vertex_count"])]
    for edge_index, (left, right) in enumerate(tangle_edges):
        incidence[left].append(edge_index)
        incidence[right].append(edge_index)
    spokes = []
    for vertex in cap:
        external = [
            edge_index
            for edge_index in incidence[vertex]
            if not set(tangle_edges[edge_index]) <= cap_vertices
        ]
        if len(external) != 1:
            raise AssertionError("a cap vertex must have one external spoke")
        spokes.append(external[0])
    return {
        "cap_face_id": cap_face_id,
        "cap_vertices": cap,
        "removed_cap_edges": [list(edge) for edge in sorted(removed_edges)],
        "tangle_edges": [list(edge) for edge in tangle_edges],
        "incident_edges": incidence,
        "spokes": spokes,
    }


def edge_face_adjacency(graph: dict[str, Any]) -> dict[int, list[int]]:
    adjacency: dict[int, list[int]] = defaultdict(list)
    for face_id, edges in enumerate(face_edge_indices(graph)):
        for edge in edges:
            adjacency[edge].append(face_id)
    if any(len(faces) != 2 for faces in adjacency.values()):
        raise AssertionError("every spherical edge must border two faces")
    return dict(adjacency)


def consistently_oriented_face_cycles(graph: dict[str, Any]) -> list[list[int]]:
    """Orient all spherical face cycles so shared edges run oppositely."""
    raw_cycles = graph["face_cycles"]
    face_edges = face_edge_indices(graph)
    edge_faces = edge_face_adjacency(graph)
    primal_edges = [tuple(edge) for edge in graph["primal_edges"]]

    def direction(cycle: list[int], edge: tuple[int, int]) -> int:
        left, right = edge
        for index, vertex in enumerate(cycle):
            successor = cycle[(index + 1) % len(cycle)]
            if vertex == left and successor == right:
                return 1
            if vertex == right and successor == left:
                return -1
        raise AssertionError("a face cycle does not traverse its listed edge")

    oriented: list[list[int] | None] = [None] * len(raw_cycles)
    oriented[0] = list(raw_cycles[0])
    queue = [0]
    cursor = 0
    while cursor < len(queue):
        face = queue[cursor]
        cursor += 1
        cycle = oriented[face]
        if cycle is None:
            raise AssertionError("the orientation queue contains an unset face")
        for edge_index in face_edges[face]:
            incident = edge_faces[edge_index]
            neighbor = incident[0] if incident[1] == face else incident[1]
            edge = primal_edges[edge_index]
            required = -direction(cycle, edge)
            if oriented[neighbor] is None:
                candidate = list(raw_cycles[neighbor])
                if direction(candidate, edge) != required:
                    candidate = [candidate[0], *reversed(candidate[1:])]
                oriented[neighbor] = candidate
                queue.append(neighbor)
            elif direction(oriented[neighbor], edge) != required:
                raise AssertionError("the face orientations are inconsistent")
    if any(cycle is None for cycle in oriented):
        raise AssertionError("the dual face-adjacency graph is disconnected")
    return [cycle for cycle in oriented if cycle is not None]
