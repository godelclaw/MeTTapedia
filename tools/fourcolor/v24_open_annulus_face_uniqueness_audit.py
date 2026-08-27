#!/usr/bin/env python3
"""Audit global shared-interior-edge uniqueness after opening two faces.

The closed minimal-counterexample map has pairwise-unique shared face edges.
The literal annular carrier is obtained by deleting the cycle edges of two
vertex-disjoint faces while retaining their vertices as degree-one stubs.
This operation splices ambient faces together, so global pairwise uniqueness
need not survive.  The audit reconstructs the opened rotation system exactly,
traverses its face orbits, and records every distinct face pair sharing more
than one edge.

This is a falsification audit for a structural hypothesis, not a graph
catalogue.  A failure is a literal finite witness; a finite absence would not
prove the universal property.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
from typing import Any

from v24_annular_census import atomic_write_json
from v24_plantri_seed_audit import (
    generated_embeddings,
    graph_record,
    open_face_annulus,
    parse_ascii_graph,
)


SCHEMA = "fourcolor-v24-open-annulus-face-uniqueness-audit-v1"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plantri", type=Path, required=True)
    parser.add_argument("--min-primal-vertices", type=int, default=20)
    parser.add_argument("--max-primal-vertices", type=int, default=34)
    parser.add_argument("--minimum-face-length", type=int, choices=(3, 4, 5), default=5)
    parser.add_argument(
        "--triangulation-connectivity", type=int, choices=(3, 4, 5), default=5
    )
    parser.add_argument("--connected-only", action="store_true")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(
            "results/fourcolor/v24_open_annulus_face_uniqueness_audit.json"
        ),
    )
    return parser.parse_args()


def opened_rotation(
    rotations: list[list[int]], faces: list[list[int]], outer_face: int, inner_face: int
) -> list[list[int]]:
    removed = {
        tuple(sorted((cap[index], cap[(index + 1) % len(cap)])))
        for cap in (faces[outer_face], faces[inner_face])
        for index in range(len(cap))
    }
    opened = [
        [
            neighbour
            for neighbour in row
            if tuple(sorted((vertex, neighbour))) not in removed
        ]
        for vertex, row in enumerate(rotations)
    ]
    if any(not row for row in opened):
        raise AssertionError("opening the two faces isolated a vertex")
    for vertex, row in enumerate(opened):
        if len(set(row)) != len(row) or any(vertex not in opened[u] for u in row):
            raise AssertionError("the opened rotation is not a simple symmetric graph")
    return opened


def dart_face_cycles(rotations: list[list[int]]) -> list[list[tuple[int, int]]]:
    unseen = {
        (vertex, neighbour)
        for vertex, row in enumerate(rotations)
        for neighbour in row
    }
    faces: list[list[tuple[int, int]]] = []
    while unseen:
        start = min(unseen)
        dart = start
        face: list[tuple[int, int]] = []
        while True:
            if dart not in unseen:
                raise AssertionError("an opened face traversal revisited a consumed dart")
            unseen.remove(dart)
            face.append(dart)
            vertex, neighbour = dart
            around = rotations[neighbour]
            position = around.index(vertex)
            dart = (neighbour, around[(position - 1) % len(around)])
            if dart == start:
                break
        faces.append(face)
    return faces


def graph_is_connected(rotations: list[list[int]]) -> bool:
    reached = {0}
    stack = [0]
    while stack:
        vertex = stack.pop()
        for neighbour in rotations[vertex]:
            if neighbour not in reached:
                reached.add(neighbour)
                stack.append(neighbour)
    return len(reached) == len(rotations)


def shared_edge_failures(
    face_darts: list[list[tuple[int, int]]]
) -> list[dict[str, Any]]:
    boundaries = [
        {tuple(sorted(dart)) for dart in face}
        for face in face_darts
    ]
    failures = []
    for left in range(len(boundaries)):
        for right in range(left + 1, len(boundaries)):
            shared = sorted(boundaries[left] & boundaries[right])
            if len(shared) > 1:
                failures.append(
                    {
                        "left_face": left,
                        "right_face": right,
                        "left_dart_length": len(face_darts[left]),
                        "right_dart_length": len(face_darts[right]),
                        "shared_interior_edges": shared,
                    }
                )
    return failures


def audit_opening(
    rotations: list[list[int]], graph: dict[str, Any], outer_face: int, inner_face: int
) -> dict[str, Any]:
    opened = opened_rotation(rotations, graph["face_cycles"], outer_face, inner_face)
    faces = dart_face_cycles(opened)
    connected = graph_is_connected(opened)
    edge_count = sum(map(len, opened)) // 2
    component_count = 1 if connected else None
    if connected and len(opened) - edge_count + len(faces) != 2:
        raise AssertionError("a connected opened rotation failed spherical Euler equality")
    failures = shared_edge_failures(faces)
    canonical = ";".join(
        ",".join(map(str, row)) for row in opened
    )
    return {
        "outer_face": outer_face,
        "outer_length": len(graph["face_cycles"][outer_face]),
        "inner_face": inner_face,
        "connected": connected,
        "opened_rotation_hash": hashlib.sha256(canonical.encode()).hexdigest(),
        "opened_edge_count": edge_count,
        "opened_face_count": len(faces),
        "pairwise_unique_shared_interior_edges": not failures,
        "failures": failures,
        "face_dart_cycles": [
            [[left, right] for left, right in face]
            for face in faces
        ],
        "component_count_when_checked": component_count,
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    sizes: list[dict[str, Any]] = []
    first_failure: dict[str, Any] | None = None
    for primal_vertices in range(args.min_primal_vertices, args.max_primal_vertices + 1, 2):
        embeddings = list(
            generated_embeddings(
                args.plantri,
                primal_vertices,
                args.minimum_face_length,
                args.triangulation_connectivity,
            )
        )
        row = {
            "primal_vertices": primal_vertices,
            "graphs": len(embeddings),
            "openings_audited": 0,
            "connected_openings": 0,
            "pairwise_unique_successes": 0,
            "pairwise_unique_failures": 0,
        }
        for graph_index, embedding in enumerate(embeddings):
            rotations = parse_ascii_graph(embedding)
            graph = graph_record(rotations, graph_index)
            faces = graph["face_cycles"]
            for outer_face in range(len(faces)):
                for inner_face in graph["pentagon_face_ids"]:
                    if outer_face == inner_face or set(faces[outer_face]) & set(faces[inner_face]):
                        continue
                    # Cross-check connectivity against the independent Seed-audit opening.
                    *_, expected_connected = open_face_annulus(graph, outer_face, inner_face)
                    opening = audit_opening(rotations, graph, outer_face, inner_face)
                    if opening["connected"] != expected_connected:
                        raise AssertionError("the two opening implementations disagree")
                    if args.connected_only and not opening["connected"]:
                        continue
                    row["openings_audited"] += 1
                    if opening["connected"]:
                        row["connected_openings"] += 1
                    if opening["pairwise_unique_shared_interior_edges"]:
                        row["pairwise_unique_successes"] += 1
                    else:
                        row["pairwise_unique_failures"] += 1
                        if first_failure is None:
                            first_violation = opening["failures"][0]
                            first_failure = {
                                "primal_vertices": primal_vertices,
                                "graph_index": graph_index,
                                "graph_hash": graph["graph_hash"],
                                "ascii_embedding": graph["ascii_embedding"],
                                "outer_face": outer_face,
                                "outer_face_cycle": faces[outer_face],
                                "inner_face": inner_face,
                                "inner_face_cycle": faces[inner_face],
                                "opened_rotation_hash": opening[
                                    "opened_rotation_hash"
                                ],
                                "opened_edge_count": opening["opened_edge_count"],
                                "opened_face_count": opening["opened_face_count"],
                                "left_face": first_violation["left_face"],
                                "right_face": first_violation["right_face"],
                                "shared_interior_edges": first_violation[
                                    "shared_interior_edges"
                                ],
                            }
        sizes.append(row)
        print(
            f"V={primal_vertices} graphs={row['graphs']} "
            f"openings={row['openings_audited']} "
            f"unique={row['pairwise_unique_successes']} "
            f"fail={row['pairwise_unique_failures']}",
            flush=True,
        )
    return {
        "schema": SCHEMA,
        "generator": {
            "name": "plantri",
            "arguments": (
                f"-a -d -m{args.minimum_face_length} "
                f"-c{args.triangulation_connectivity} (V/2+2)"
            ),
            "binary_sha256": hashlib.sha256(args.plantri.read_bytes()).hexdigest(),
        },
        "generated_class": (
            "simple cubic spherical maps dual to the requested triangulations"
        ),
        "connected_only": args.connected_only,
        "sizes": sizes,
        "first_failure": first_failure,
        "scope_warning": (
            "This refutes global pairwise uniqueness on the recorded literal "
            "opened annulus.  It does not refute local uniqueness for two fully "
            "retained ambient face images."
        ),
    }


def main() -> int:
    args = parse_args()
    result = run(args)
    atomic_write_json(args.output, result)
    print(f"certificate={args.output}")
    return 1 if result["first_failure"] is not None else 0


if __name__ == "__main__":
    raise SystemExit(main())
