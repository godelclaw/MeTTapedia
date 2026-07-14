#!/usr/bin/env python3
"""Verify v24 deep-desert and Short-Strand refutation specimens."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter, deque
from pathlib import Path
from typing import Any

from v24_annular_census import atomic_write_json
from v24_annular_kempe import COLOR_PAIRS, bichromatic_components, is_good_word
from v24_goldberg import (
    cap_distances,
    consistently_oriented_face_cycles,
    face_edge_indices,
    make_cap_tangle,
    make_goldberg_graph,
)


SCHEMA = "fourcolor-v24-specimen-audit-v1"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Audit the archived v24 desert and strand specimens."
    )
    parser.add_argument("--specimen-dir", required=True, type=Path)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_specimen_audit.json"),
    )
    return parser.parse_args()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def proper_partial_coloring(
    edges: list[tuple[int, int]], colors: dict[tuple[int, int], int]
) -> bool:
    used: dict[int, set[int]] = {}
    for edge in edges:
        if edge not in colors:
            continue
        color = colors[edge]
        if color not in range(3):
            return False
        for vertex in edge:
            vertex_used = used.setdefault(vertex, set())
            if color in vertex_used:
                return False
            vertex_used.add(color)
    return True


def deep_constraint_sets(
    face_ids: list[int], face_edges: list[list[int]]
) -> list[frozenset[int]]:
    result = [frozenset(face_edges[face]) for face in face_ids]
    edge_faces: dict[int, list[int]] = {}
    for face in face_ids:
        for edge in face_edges[face]:
            edge_faces.setdefault(edge, []).append(face)
    adjacency = {face: set() for face in face_ids}
    for incident_faces in edge_faces.values():
        if len(incident_faces) == 2:
            left, right = incident_faces
            adjacency[left].add(right)
            adjacency[right].add(left)
    for left in face_ids:
        for right in adjacency[left]:
            if right <= left:
                continue
            if len(face_edges[left]) == len(face_edges[right]) == 6:
                boundary = frozenset(face_edges[left]) ^ frozenset(face_edges[right])
                if len(boundary) != 10:
                    raise AssertionError("a fused hexagon pair must have ten edges")
                result.append(boundary)
    for middle in face_ids:
        if len(face_edges[middle]) != 6:
            continue
        for left, right in itertools.combinations(sorted(adjacency[middle]), 2):
            if right in adjacency[left]:
                continue
            if len(face_edges[left]) != 6 or len(face_edges[right]) != 6:
                continue
            boundary = (
                frozenset(face_edges[left])
                ^ frozenset(face_edges[middle])
                ^ frozenset(face_edges[right])
            )
            if len(boundary) == 14:
                result.append(boundary)
    return result


def winding(colors: list[int]) -> int:
    score = 0
    for left, right in zip(colors, colors[1:] + colors[:1], strict=True):
        if right == (left + 1) % 3:
            score += 1
        elif left == (right + 1) % 3:
            score -= 1
        else:
            raise AssertionError("consecutive face edges share a color")
    if score % 3:
        raise AssertionError("the face winding score is not divisible by three")
    return score // 3


def audit_deep_patches(
    specimen_dir: Path, graph: dict[str, Any]
) -> list[dict[str, Any]]:
    edges = [tuple(edge) for edge in graph["primal_edges"]]
    edge_index = {edge: index for index, edge in enumerate(edges)}
    face_edges = face_edge_indices(graph)
    oriented_cycles = consistently_oriented_face_cycles(graph)
    certificate_cycles = graph["certificate_face_cycles"]
    cap_face = graph["pentagon_face_ids"][0]
    distances = cap_distances(graph, cap_face)
    rows = []
    for radius in range(2, 9):
        path = specimen_dir / f"deep_patch_R{radius}.json"
        data = load_json(path)
        colors = {
            tuple(map(int, edge.split(","))): int(color)
            for edge, color in data["colors"].items()
        }
        expected_patch_edges = {
            edge
            for edge in edges
            if distances[edge[0]] <= radius + 2
            and distances[edge[1]] <= radius + 2
        }
        constrained_faces = [
            face
            for face, cycle in enumerate(graph["face_cycles"])
            if len(cycle) == 6
            and max(distances[vertex] for vertex in cycle) <= radius
        ]
        constraints = deep_constraint_sets(constrained_faces, face_edges)
        every_constraint_rainbow = all(
            {colors[edges[edge]] for edge in constraint} == {0, 1, 2}
            for constraint in constraints
        )

        def face_winding(cycles: list[list[int]], face: int) -> int:
            cycle = cycles[face]
            return winding(
                [
                    colors[
                        tuple(
                            sorted(
                                (
                                    cycle[index],
                                    cycle[(index + 1) % len(cycle)],
                                )
                            )
                        )
                    ]
                    for index in range(len(cycle))
                ]
            )

        certificate_winding_histogram = Counter(
            face_winding(certificate_cycles, face) for face in constrained_faces
        )
        oriented_winding_histogram = Counter(
            face_winding(oriented_cycles, face) for face in constrained_faces
        )
        chiral_count = sum(
            count
            for value, count in oriented_winding_histogram.items()
            if value != 0
        )
        rows.append(
            {
                "source_file": path.name,
                "source_sha256": file_sha256(path),
                "radius": radius,
                "patch_edge_count": len(colors),
                "patch_edge_set_exact": set(colors) == expected_patch_edges,
                "proper_partial_coloring": proper_partial_coloring(edges, colors),
                "constrained_face_count": len(constrained_faces),
                "deep_constraint_count": len(constraints),
                "every_deep_constraint_uses_all_three_colors": (
                    every_constraint_rainbow
                ),
                "certificate_order_winding_histogram": {
                    str(value): count
                    for value, count in sorted(
                        certificate_winding_histogram.items()
                    )
                },
                "globally_oriented_winding_histogram": {
                    str(value): count
                    for value, count in sorted(oriented_winding_histogram.items())
                },
                "chiral_hexagon_count": chiral_count,
                "melted_hexagon_count": len(constrained_faces) - chiral_count,
                "all_constraint_edges_present": all(
                    all(edges[edge] in colors for edge in constraint)
                    for constraint in constraints
                ),
                "edge_index_digest": hashlib.sha256(
                    b"".join(
                        edge_index[edge].to_bytes(2, "big")
                        + bytes([colors[edge]])
                        for edge in sorted(colors)
                    )
                ).hexdigest(),
            }
        )
    return rows


def follow_stub_path(
    tangle: dict[str, Any], coloring: bytes, stub: int, pair: tuple[int, int]
) -> tuple[int, frozenset[int], frozenset[int]]:
    edges = [tuple(edge) for edge in tangle["tangle_edges"]]
    incidence = tangle["incident_edges"]
    cap = tangle["cap_vertices"]
    edge = tangle["spokes"][stub]
    if coloring[edge] not in pair:
        raise AssertionError("the stub color is not active for this pair")
    current = cap[stub]
    path_edges = set()
    path_vertices = {current}
    while True:
        path_edges.add(edge)
        left, right = edges[edge]
        current = right if left == current else left
        path_vertices.add(current)
        if len(incidence[current]) == 1:
            return cap.index(current), frozenset(path_edges), frozenset(path_vertices)
        next_edges = [
            candidate
            for candidate in incidence[current]
            if candidate != edge and coloring[candidate] in pair
        ]
        if len(next_edges) != 1:
            raise AssertionError("an internal bichromatic path does not continue uniquely")
        edge = next_edges[0]


def tangle_deep_constraints(
    graph: dict[str, Any], tangle: dict[str, Any], radius: int
) -> list[frozenset[int]]:
    full_edges = [tuple(edge) for edge in graph["primal_edges"]]
    tangle_edges = [tuple(edge) for edge in tangle["tangle_edges"]]
    tangle_edge_index = {edge: index for index, edge in enumerate(tangle_edges)}
    distances = cap_distances(graph, tangle["cap_face_id"])
    full_face_edges = face_edge_indices(graph)
    face_edges: list[list[int]] = [[] for _ in graph["face_cycles"]]
    constrained_faces = []
    for face, cycle in enumerate(graph["face_cycles"]):
        boundary = [full_edges[edge] for edge in full_face_edges[face]]
        if (
            len(cycle) == 6
            and max(distances[vertex] for vertex in cycle) <= radius
            and all(edge in tangle_edge_index for edge in boundary)
        ):
            constrained_faces.append(face)
            face_edges[face] = [tangle_edge_index[edge] for edge in boundary]
    return deep_constraint_sets(constrained_faces, face_edges)


def unlock_within_radius(
    tangle: dict[str, Any], start: bytes, distances: list[int], radius: int
) -> tuple[bool, int, list[dict[str, Any]]]:
    edges = [tuple(edge) for edge in tangle["tangle_edges"]]
    incidence = tangle["incident_edges"]
    ball_edges = {
        edge
        for edge, (left, right) in enumerate(edges)
        if distances[left] <= radius and distances[right] <= radius
    }
    start_key = bytes(start[edge] for edge in sorted(ball_edges))
    queue = deque([start])
    parents: dict[bytes, tuple[bytes, dict[str, Any]] | None] = {start_key: None}
    while queue:
        coloring = queue.popleft()
        for pair in COLOR_PAIRS:
            for component in bichromatic_components(coloring, pair, edges, incidence):
                if not component <= ball_edges:
                    continue
                switched = bytearray(coloring)
                left_color, right_color = pair
                for edge in component:
                    switched[edge] = (
                        right_color
                        if switched[edge] == left_color
                        else left_color
                    )
                target = bytes(switched)
                key = bytes(target[edge] for edge in sorted(ball_edges))
                if key in parents:
                    continue
                move = {
                    "color_pair": "".join(map(str, pair)),
                    "component_edge_count": len(component),
                    "component_edge_indices": sorted(component),
                }
                parents[key] = (
                    bytes(coloring[edge] for edge in sorted(ball_edges)),
                    move,
                )
                word = tuple(target[edge] for edge in tangle["spokes"])
                if is_good_word(word):
                    moves = []
                    cursor = key
                    while parents[cursor] is not None:
                        previous, step = parents[cursor]
                        moves.append(step)
                        cursor = previous
                    moves.reverse()
                    return True, len(parents), moves
                queue.append(target)
    return False, len(parents), []


def audit_short_strand(
    specimen_dir: Path, graph: dict[str, Any]
) -> dict[str, Any]:
    path = specimen_dir / "conjecture_counterexample.json"
    raw = load_json(path)
    coloring = bytes(map(int, raw))
    cap_face = graph["pentagon_face_ids"][0]
    tangle = make_cap_tangle(graph, cap_face)
    edges = [tuple(edge) for edge in tangle["tangle_edges"]]
    incidence = tangle["incident_edges"]
    if len(coloring) != len(edges):
        raise AssertionError("the Short-Strand specimen has the wrong edge count")
    proper = all(
        len({coloring[edge] for edge in incident}) == len(incident)
        for incident in incidence
    )
    word = tuple(coloring[edge] for edge in tangle["spokes"])
    distances = cap_distances(graph, cap_face)
    strands = []
    seen = set()
    for stub, spoke in enumerate(tangle["spokes"]):
        for pair in COLOR_PAIRS:
            if coloring[spoke] not in pair:
                continue
            target, path_edges, path_vertices = follow_stub_path(
                tangle, coloring, stub, pair
            )
            key = (pair, min(stub, target), max(stub, target))
            if key in seen:
                continue
            seen.add(key)
            strands.append(
                {
                    "color_pair": "".join(map(str, pair)),
                    "stub_endpoints": [min(stub, target), max(stub, target)],
                    "edge_count": len(path_edges),
                    "reach": max(distances[vertex] for vertex in path_vertices),
                    "edge_index_digest": hashlib.sha256(
                        b"".join(edge.to_bytes(2, "big") for edge in sorted(path_edges))
                    ).hexdigest(),
                }
            )
    strands.sort(key=lambda row: (row["color_pair"], row["stub_endpoints"]))

    deep_constraints = tangle_deep_constraints(graph, tangle, 7)
    deep_constraints_hold = all(
        {coloring[edge] for edge in constraint} == {0, 1, 2}
        for constraint in deep_constraints
    )
    radius_rows = []
    unlock_moves = []
    for radius in range(0, 9):
        unlocked, state_count, moves = unlock_within_radius(
            tangle, coloring, distances, radius
        )
        radius_rows.append(
            {
                "radius": radius,
                "reachable_state_count": state_count,
                "reaches_good_word": unlocked,
            }
        )
        if unlocked:
            unlock_moves = moves
            break
    return {
        "source_file": path.name,
        "source_sha256": file_sha256(path),
        "graph_frequency": graph["frequency"],
        "graph_hash": graph["graph_hash"],
        "tangle_edge_count": len(edges),
        "proper_tait_coloring": proper,
        "boundary_word": "".join(map(str, word)),
        "exceptional_pairing_01": [
            row["stub_endpoints"]
            for row in strands
            if row["color_pair"] == "01"
        ],
        "exceptional_pairing_02": [
            row["stub_endpoints"]
            for row in strands
            if row["color_pair"] == "02"
        ],
        "necklace_strands": strands,
        "deep_desert_radius": 7,
        "deep_constraint_count": len(deep_constraints),
        "every_deep_constraint_uses_all_three_colors": deep_constraints_hold,
        "unlock_radius_audit": radius_rows,
        "minimum_unlock_radius_found": (
            radius_rows[-1]["radius"]
            if radius_rows[-1]["reaches_good_word"]
            else None
        ),
        "unlock_moves": unlock_moves,
    }


def main() -> int:
    args = parse_args()
    graph = make_goldberg_graph(8)
    result = {
        "schema": SCHEMA,
        "algorithm": "explicit-goldberg-and-direct-constraint-audit-v1",
        "graph": {
            "frequency": graph["frequency"],
            "graph_hash": graph["graph_hash"],
            "vertex_count": graph["primal_vertex_count"],
            "edge_count": len(graph["primal_edges"]),
            "face_count": len(graph["face_cycles"]),
        },
        "deep_patches": audit_deep_patches(args.specimen_dir, graph),
        "short_strand_counterexample": audit_short_strand(
            args.specimen_dir, graph
        ),
    }
    atomic_write_json(args.output, result)
    short = result["short_strand_counterexample"]
    print(
        f"deep patches: {len(result['deep_patches'])}; short-strand lengths "
        f"{[row['edge_count'] for row in short['necklace_strands']]}; "
        f"unlock radius {short['minimum_unlock_radius_found']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
