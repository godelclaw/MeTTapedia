#!/usr/bin/env python3
"""Search a generated small plane-map class for a Seed-Lemma counterexample.

By default, plantri -m5 -c5 enumerates 5-connected spherical
triangulations of minimum degree five.  Their planar duals are the generated
simple cubic plane maps with face length at least five and cyclic
edge-connectivity at least five.  The face-length and connectivity flags may
be weakened deliberately to audit which normal-form hypotheses are
load-bearing.  For each generated map, this audit opens every ordered pair
consisting of a pentagonal inner face and an arbitrary vertex-disjoint outer
face, then asks the cap-correct Seed question for all ten good inner words
modulo a global colour permutation.

The SAT encoding and independent literal witness replay are imported from
``v24_goldberg_seed_sat``.  Only aggregate counts and any seedless witnesses
are retained: this is a route-native falsification audit, not a configuration
catalogue and not a proof of the universal Seed Lemma.
"""

from __future__ import annotations

import argparse
import hashlib
import subprocess
from collections import deque
from pathlib import Path
from typing import Any, Iterable

import z3

from v24_annular_census import atomic_write_json
from v24_goldberg_seed_sat import (
    GOOD_WORDS,
    literal_menu_b,
    menu_b_formula,
    proper_colouring_solver,
)


SCHEMA = "fourcolor-v24-plantri-seed-audit-v2"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plantri", type=Path, required=True)
    parser.add_argument(
        "--min-primal-vertices",
        type=int,
        default=20,
        help="smallest even order of a generated cubic plane map",
    )
    parser.add_argument(
        "--max-primal-vertices",
        type=int,
        default=36,
        help="largest even order of a generated cubic plane map",
    )
    parser.add_argument(
        "--minimum-face-length",
        type=int,
        choices=(3, 4, 5),
        default=5,
        help="minimum primal face length (minimum degree in the generated dual)",
    )
    parser.add_argument(
        "--triangulation-connectivity",
        type=int,
        choices=(3, 4, 5),
        default=5,
        help="connectivity requested from plantri before dualizing",
    )
    parser.add_argument(
        "--connected-only",
        action="store_true",
        help="report a seedless witness only when the opened annulus is connected",
    )
    parser.add_argument(
        "--stop-on-first",
        action="store_true",
        help="stop as soon as a seedless nonempty good fibre is found",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_plantri_seed_audit.json"),
    )
    return parser.parse_args()


def parse_ascii_graph(line: str) -> list[list[int]]:
    """Parse plantri's one-byte ASCII embedding at the small orders used here."""
    order_text, rows_text = line.strip().split(maxsplit=1)
    order = int(order_text)
    rows = rows_text.split(",")
    if len(rows) != order:
        raise ValueError(f"expected {order} rotation rows, found {len(rows)}")
    base = ord("a")
    rotations = [[ord(name) - base for name in row] for row in rows]
    if any(not (0 <= neighbour < order) for row in rotations for neighbour in row):
        raise ValueError("the ASCII embedding uses a vertex name outside its order")
    if any(len(row) != 3 for row in rotations):
        raise ValueError("the requested dual is not cubic")
    for vertex, row in enumerate(rotations):
        if len(set(row)) != 3 or any(vertex not in rotations[u] for u in row):
            raise ValueError("the ASCII embedding is not a simple symmetric cubic graph")
    return rotations


def face_cycles(rotations: list[list[int]]) -> list[list[int]]:
    """Traverse every oriented face of a rotation system exactly once."""
    unseen = {(vertex, neighbour) for vertex, row in enumerate(rotations) for neighbour in row}
    faces: list[list[int]] = []
    while unseen:
        start = min(unseen)
        dart = start
        face: list[int] = []
        while True:
            if dart not in unseen:
                raise AssertionError("a face traversal met a previously consumed dart")
            unseen.remove(dart)
            vertex, neighbour = dart
            face.append(vertex)
            around = rotations[neighbour]
            position = around.index(vertex)
            # With clockwise vertex rotations, predecessor keeps one chosen
            # face consistently on the same side of the directed dart.
            dart = (neighbour, around[(position - 1) % len(around)])
            if dart == start:
                break
        faces.append(face)
    order = len(rotations)
    edge_count = sum(map(len, rotations)) // 2
    if order - edge_count + len(faces) != 2:
        raise AssertionError("the parsed embedding does not satisfy spherical Euler equality")
    if sum(map(len, faces)) != 2 * edge_count:
        raise AssertionError("the parsed faces do not use every dart once")
    return faces


def graph_record(rotations: list[list[int]], graph_index: int) -> dict[str, Any]:
    edges = sorted(
        (vertex, neighbour)
        for vertex, row in enumerate(rotations)
        for neighbour in row
        if vertex < neighbour
    )
    faces = face_cycles(rotations)
    canonical_text = ";".join(
        ",".join(map(str, row)) for row in rotations
    )
    return {
        "frequency": graph_index,
        "primal_vertex_count": len(rotations),
        "primal_edges": edges,
        "face_cycles": faces,
        "pentagon_face_ids": [index for index, face in enumerate(faces) if len(face) == 5],
        "graph_hash": hashlib.sha256(canonical_text.encode()).hexdigest(),
        "ascii_embedding": f"{len(rotations)} " + ",".join(
            "".join(chr(ord("a") + neighbour) for neighbour in row)
            for row in rotations
        ),
    }


def open_face_annulus(
    graph: dict[str, Any], outer_face: int, inner_face: int
) -> tuple[list[tuple[int, int]], list[list[int]], list[int], list[int], bool]:
    """Open a pentagonal inner face and an arbitrary disjoint outer face."""
    faces = graph["face_cycles"]
    outer_cap = faces[outer_face]
    inner_cap = faces[inner_face]
    if len(inner_cap) != 5:
        raise ValueError("the Seed inner cap must be pentagonal")
    if set(outer_cap) & set(inner_cap):
        raise ValueError("the two boundary faces are not vertex-disjoint")
    removed = {
        tuple(sorted((cap[index], cap[(index + 1) % len(cap)])))
        for cap in (outer_cap, inner_cap)
        for index in range(len(cap))
    }
    edges = [tuple(edge) for edge in graph["primal_edges"] if tuple(edge) not in removed]
    incidence = [[] for _ in range(graph["primal_vertex_count"])]
    for edge_index, (left, right) in enumerate(edges):
        incidence[left].append(edge_index)
        incidence[right].append(edge_index)
    def boundary_spokes(cap: list[int]) -> list[int]:
        cap_set = set(cap)
        spokes: list[int] = []
        for vertex in cap:
            candidates = [
                edge_index
                for edge_index in incidence[vertex]
                if any(endpoint not in cap_set for endpoint in edges[edge_index])
            ]
            if len(candidates) != 1:
                raise AssertionError("an opened face vertex does not have one spoke")
            spokes.append(candidates[0])
        if len(set(spokes)) != len(cap):
            raise AssertionError("distinct opened face vertices do not have distinct spokes")
        return spokes

    inner_spokes = boundary_spokes(inner_cap)
    boundary_spokes(outer_cap)

    reached = {0}
    queue = deque([0])
    adjacency = [set() for _ in incidence]
    for left, right in edges:
        adjacency[left].add(right)
        adjacency[right].add(left)
    while queue:
        vertex = queue.popleft()
        for neighbour in adjacency[vertex] - reached:
            reached.add(neighbour)
            queue.append(neighbour)
    connected = len(reached) == len(incidence)
    return edges, incidence, inner_spokes, inner_cap, connected


def audit_face_annulus(
    graph: dict[str, Any], outer_face: int, inner_face: int
) -> dict[str, Any]:
    edges, incidence, inner_spokes, inner_cap, connected = open_face_annulus(
        graph, outer_face, inner_face
    )
    tag = f"g{graph['frequency']}_o{outer_face}_i{inner_face}"
    solver, colours = proper_colouring_solver(edges, incidence, tag)
    nonempty: list[str] = []
    seeded: list[str] = []
    seedless: list[str] = []
    for word in GOOD_WORDS:
        word_key = "".join(map(str, word))
        solver.push()
        solver.add(*(colours[edge] == colour for edge, colour in zip(inner_spokes, word)))
        plain_status = solver.check()
        if str(plain_status) == "unknown":
            raise RuntimeError(f"SAT returned unknown on {tag}, word {word_key}")
        if str(plain_status) == "sat":
            nonempty.append(word_key)
            solver.push()
            solver.add(
                menu_b_formula(
                    edges, incidence, colours, inner_spokes, inner_cap, word, tag
                )
            )
            menu_status = solver.check()
            if str(menu_status) == "unknown":
                raise RuntimeError(f"SAT returned unknown on Menu B for {tag}, {word_key}")
            if str(menu_status) == "sat":
                model = solver.model()
                colouring = tuple(model.eval(colour).as_long() for colour in colours)
                if not literal_menu_b(
                    colouring, edges, incidence, inner_spokes, inner_cap, word
                ):
                    raise AssertionError(
                        f"the SAT Menu-B witness failed literal replay: {tag}, {word_key}"
                    )
                seeded.append(word_key)
            else:
                seedless.append(word_key)
            solver.pop()
        solver.pop()
    return {
        "outer_face": outer_face,
        "outer_length": len(graph["face_cycles"][outer_face]),
        "inner_face": inner_face,
        "connected": connected,
        "nonempty_good_words": nonempty,
        "seeded_good_words": seeded,
        "seedless_good_words": seedless,
    }


def generated_embeddings(
    plantri: Path,
    primal_vertices: int,
    minimum_face_length: int = 5,
    triangulation_connectivity: int = 5,
) -> Iterable[str]:
    if primal_vertices % 2 or primal_vertices < 4:
        raise ValueError("the cubic order must be even and at least four")
    triangulation_vertices = primal_vertices // 2 + 2
    command = [
        str(plantri),
        "-a",
        "-d",
        f"-m{minimum_face_length}",
        f"-c{triangulation_connectivity}",
        str(triangulation_vertices),
    ]
    # plantri's small ASCII format uses consecutive one-byte vertex names;
    # already at order 32 the last name is byte 0x80, which is not UTF-8.
    completed = subprocess.run(
        command, check=True, text=True, encoding="latin-1", capture_output=True
    )
    for line in completed.stdout.splitlines():
        if line.strip():
            yield line


def audit_graph(
    graph: dict[str, Any], stop_on_first: bool, connected_only: bool = False
) -> dict[str, Any]:
    pentagons = graph["pentagon_face_ids"]
    ordered_boundary_instances = 0
    connected_annuli = 0
    disconnected_boundary_instances = 0
    nonempty = 0
    seeded = 0
    connected_nonempty = 0
    connected_seeded = 0
    seedless: list[dict[str, Any]] = []
    outer_length_counts: dict[int, int] = {}
    for outer_face in range(len(graph["face_cycles"])):
        for inner_face in pentagons:
            if outer_face == inner_face:
                continue
            if set(graph["face_cycles"][outer_face]) & set(graph["face_cycles"][inner_face]):
                continue
            row = audit_face_annulus(graph, outer_face, inner_face)
            ordered_boundary_instances += 1
            if row["connected"]:
                connected_annuli += 1
                connected_nonempty += len(row["nonempty_good_words"])
                connected_seeded += len(row["seeded_good_words"])
            else:
                disconnected_boundary_instances += 1
            outer_length = row["outer_length"]
            outer_length_counts[outer_length] = outer_length_counts.get(outer_length, 0) + 1
            nonempty += len(row["nonempty_good_words"])
            seeded += len(row["seeded_good_words"])
            if row["seedless_good_words"] and (row["connected"] or not connected_only):
                seedless.append(row)
                if stop_on_first:
                    return {
                        "ordered_boundary_instances_audited": ordered_boundary_instances,
                        "connected_annuli_audited": connected_annuli,
                        "disconnected_boundary_instances_audited":
                            disconnected_boundary_instances,
                        "nonempty_good_fibres": nonempty,
                        "seeded_good_fibres": seeded,
                        "connected_nonempty_good_fibres": connected_nonempty,
                        "connected_seeded_good_fibres": connected_seeded,
                        "seedless": seedless,
                        "outer_length_counts": outer_length_counts,
                    }
    return {
        "ordered_boundary_instances_audited": ordered_boundary_instances,
        "connected_annuli_audited": connected_annuli,
        "disconnected_boundary_instances_audited": disconnected_boundary_instances,
        "nonempty_good_fibres": nonempty,
        "seeded_good_fibres": seeded,
        "connected_nonempty_good_fibres": connected_nonempty,
        "connected_seeded_good_fibres": connected_seeded,
        "seedless": seedless,
        "outer_length_counts": outer_length_counts,
    }


def run(
    plantri: Path,
    min_primal_vertices: int,
    max_primal_vertices: int,
    stop_on_first: bool,
    minimum_face_length: int = 5,
    triangulation_connectivity: int = 5,
    connected_only: bool = False,
) -> dict[str, Any]:
    if not plantri.is_file():
        raise FileNotFoundError(plantri)
    sizes: list[dict[str, Any]] = []
    first_witness: dict[str, Any] | None = None
    if min_primal_vertices < 4 or min_primal_vertices % 2:
        raise ValueError("the minimum cubic order must be even and at least four")
    for primal_vertices in range(min_primal_vertices, max_primal_vertices + 1, 2):
        graphs = list(
            generated_embeddings(
                plantri,
                primal_vertices,
                minimum_face_length,
                triangulation_connectivity,
            )
        )
        size_row: dict[str, Any] = {
            "primal_vertices": primal_vertices,
            "graphs": len(graphs),
            "ordered_boundary_instances_audited": 0,
            "connected_annuli_audited": 0,
            "disconnected_boundary_instances_audited": 0,
            "nonempty_good_fibres": 0,
            "seeded_good_fibres": 0,
            "connected_nonempty_good_fibres": 0,
            "connected_seeded_good_fibres": 0,
            "seedless_good_fibres": 0,
            "outer_length_counts": {},
        }
        for graph_index, embedding in enumerate(graphs):
            graph = graph_record(parse_ascii_graph(embedding), graph_index)
            row = audit_graph(graph, stop_on_first, connected_only)
            size_row["ordered_boundary_instances_audited"] += row[
                "ordered_boundary_instances_audited"
            ]
            size_row["connected_annuli_audited"] += row["connected_annuli_audited"]
            size_row["disconnected_boundary_instances_audited"] += row[
                "disconnected_boundary_instances_audited"
            ]
            size_row["nonempty_good_fibres"] += row["nonempty_good_fibres"]
            size_row["seeded_good_fibres"] += row["seeded_good_fibres"]
            size_row["connected_nonempty_good_fibres"] += row[
                "connected_nonempty_good_fibres"
            ]
            size_row["connected_seeded_good_fibres"] += row[
                "connected_seeded_good_fibres"
            ]
            size_row["seedless_good_fibres"] += sum(
                len(witness["seedless_good_words"]) for witness in row["seedless"]
            )
            for length, count in row["outer_length_counts"].items():
                key = str(length)
                size_row["outer_length_counts"][key] = (
                    size_row["outer_length_counts"].get(key, 0) + count
                )
            if row["seedless"] and first_witness is None:
                first_witness = {
                    "primal_vertices": primal_vertices,
                    "graph_index": graph_index,
                    "graph_hash": graph["graph_hash"],
                    "ascii_embedding": graph["ascii_embedding"],
                    "face_cycles": graph["face_cycles"],
                    "annulus": row["seedless"][0],
                }
                if stop_on_first:
                    break
        sizes.append(size_row)
        print(
            f"V={primal_vertices} graphs={size_row['graphs']} "
            f"pairs={size_row['ordered_boundary_instances_audited']} "
            f"connected={size_row['connected_annuli_audited']} "
            f"nonempty={size_row['nonempty_good_fibres']} "
            f"seeded={size_row['seeded_good_fibres']} "
            f"seedless={size_row['seedless_good_fibres']}",
            flush=True,
        )
        if first_witness is not None and stop_on_first:
            break
    return {
        "schema": SCHEMA,
        "generator": {
            "name": "plantri",
            "version": "5.8 (2026-03-04)",
            "source": "https://users.cecs.anu.edu.au/~bdm/plantri/",
            "arguments": (
                f"-a -d -m{minimum_face_length} "
                f"-c{triangulation_connectivity} (V/2+2)"
            ),
            "binary_sha256": hashlib.sha256(plantri.read_bytes()).hexdigest(),
        },
        "solver": f"z3-{z3.get_version_string()}",
        "good_word_representatives": [
            "".join(map(str, word)) for word in GOOD_WORDS
        ],
        "colour_symmetry": (
            "majority fixed to 0; all global colour permutations represented"
        ),
        "generated_class": (
            "duals of spherical triangulations with minimum degree "
            f"{minimum_face_length} and requested connectivity "
            f"{triangulation_connectivity}: simple cubic plane maps with "
            f"face length >={minimum_face_length}"
        ),
        "counterexample_scope": (
            "connected opened annuli only" if connected_only
            else "all well-formed opened boundary data, including disconnected"
        ),
        "sizes": sizes,
        "first_seedless_witness": first_witness,
        "scope_warning": (
            "Exhaustive only through the requested finite order; SAT witnesses are "
            "replayed literally, but absence of a witness is not a universal proof."
        ),
    }


def main() -> int:
    args = parse_args()
    result = run(
        args.plantri,
        args.min_primal_vertices,
        args.max_primal_vertices,
        args.stop_on_first,
        args.minimum_face_length,
        args.triangulation_connectivity,
        args.connected_only,
    )
    atomic_write_json(args.output, result)
    print(f"certificate={args.output}")
    return 1 if result["first_seedless_witness"] is not None else 0


if __name__ == "__main__":
    raise SystemExit(main())
