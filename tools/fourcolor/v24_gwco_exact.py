#!/usr/bin/env python3
"""Enumerate the v24 Good-Word Circuit Obstruction exact system."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import deque
from pathlib import Path
from typing import Iterable, Iterator

from v24_annular_census import atomic_write_json


SCHEMA = "fourcolor-v24-gwco-exact-base-v1"
COLOR_COUNT = 3
STUB_COUNT = 10
INNER_STUB_OFFSETS = tuple(range(5))
OUTER_STUB_OFFSETS = tuple(range(5, 10))

Matching = tuple[int, ...]
Edge = tuple[int, int]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Exhaust the v24 three-matchings GWCO system."
    )
    parser.add_argument(
        "--sizes", type=int, nargs="+", default=[6, 8, 10]
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_gwco_exact_base.json"),
    )
    return parser.parse_args()


def perfect_matchings(vertices: tuple[int, ...]) -> Iterator[tuple[Edge, ...]]:
    if not vertices:
        yield ()
        return
    left = vertices[0]
    for index in range(1, len(vertices)):
        right = vertices[index]
        remaining = vertices[1:index] + vertices[index + 1 :]
        for tail in perfect_matchings(remaining):
            yield ((left, right), *tail)


def matching_from_edges(vertex_count: int, edges: Iterable[Edge]) -> Matching:
    partner = [-1] * (vertex_count + STUB_COUNT)
    for left, right in edges:
        if partner[left] != -1 or partner[right] != -1:
            raise AssertionError("a color class is not a matching")
        partner[left] = right
        partner[right] = left
    return tuple(partner)


def matching_edges(matching: Matching) -> tuple[Edge, ...]:
    return tuple(
        (left, right)
        for left, right in enumerate(matching)
        if right > left
    )


def terminal_sets(vertex_count: int) -> tuple[tuple[int, ...], ...]:
    inner = tuple(vertex_count + offset for offset in INNER_STUB_OFFSETS)
    outer = tuple(vertex_count + offset for offset in OUTER_STUB_OFFSETS)
    alpha = (*inner[:3], *outer[:3])
    beta = (inner[3], outer[3])
    gamma = (inner[4], outer[4])
    return inner, outer, alpha, beta, gamma


def canonical_alpha_matching(vertex_count: int) -> Matching:
    _, _, alpha_stubs, _, _ = terminal_sets(vertex_count)
    if vertex_count < len(alpha_stubs) or vertex_count % 2:
        raise ValueError("the exact system requires an even size of at least six")
    edges = [(vertex, stub) for vertex, stub in enumerate(alpha_stubs)]
    edges.extend(
        (vertex, vertex + 1) for vertex in range(len(alpha_stubs), vertex_count, 2)
    )
    return matching_from_edges(vertex_count, edges)


def two_stub_matchings(
    vertex_count: int, stubs: tuple[int, int]
) -> Iterator[Matching]:
    for inner_endpoint in range(vertex_count):
        for outer_endpoint in range(vertex_count):
            if inner_endpoint == outer_endpoint:
                continue
            remaining = tuple(
                vertex
                for vertex in range(vertex_count)
                if vertex not in (inner_endpoint, outer_endpoint)
            )
            for internal_edges in perfect_matchings(remaining):
                yield matching_from_edges(
                    vertex_count,
                    (
                        (inner_endpoint, stubs[0]),
                        (outer_endpoint, stubs[1]),
                        *internal_edges,
                    ),
                )


def edge_set(matching: Matching) -> frozenset[Edge]:
    return frozenset(matching_edges(matching))


def pair_is_simple(left: Matching, right: Matching) -> bool:
    return edge_set(left).isdisjoint(edge_set(right))


def pair_is_radial_forest(
    vertex_count: int,
    left: Matching,
    right: Matching,
    terminals: tuple[int, ...],
) -> bool:
    active = set(range(vertex_count)) | set(terminals)
    adjacency = {vertex: [] for vertex in active}
    for matching in (left, right):
        for u, v in matching_edges(matching):
            if u in active and v in active:
                adjacency[u].append(v)
                adjacency[v].append(u)
    if any(len(adjacency[vertex]) != 2 for vertex in range(vertex_count)):
        return False
    if any(len(adjacency[stub]) != 1 for stub in terminals):
        return False

    visited: set[int] = set()
    for start in terminals:
        if start in visited:
            continue
        previous = -1
        current = start
        while True:
            if current in visited:
                return False
            visited.add(current)
            choices = [
                neighbor
                for neighbor in adjacency[current]
                if neighbor != previous
            ]
            if not choices:
                break
            if len(choices) != 1:
                return False
            previous, current = current, choices[0]
        if current < vertex_count:
            return False
        if (start - vertex_count) // 5 == (current - vertex_count) // 5:
            return False
    return visited == active


def matching_candidates(
    vertex_count: int,
    alpha: Matching,
    alpha_stubs: tuple[int, ...],
    color_stubs: tuple[int, int],
) -> list[Matching]:
    return [
        matching
        for matching in two_stub_matchings(vertex_count, color_stubs)
        if pair_is_simple(alpha, matching)
        and pair_is_radial_forest(
            vertex_count,
            alpha,
            matching,
            (*alpha_stubs, *color_stubs),
        )
    ]


def alpha_stabilizer(vertex_count: int) -> list[tuple[int, ...]]:
    _, _, alpha_stubs, _, _ = terminal_sets(vertex_count)
    blocks = tuple((left, left + 1) for left in range(6, vertex_count, 2))
    permutations = []
    for inner_order in itertools.permutations(range(3)):
        for outer_order in itertools.permutations(range(3, 6)):
            foot_order = (*inner_order, *outer_order)
            for block_order in itertools.permutations(range(len(blocks))):
                for flips in itertools.product((False, True), repeat=len(blocks)):
                    image = list(range(vertex_count + STUB_COUNT))
                    for source, target in enumerate(foot_order):
                        image[source] = target
                        image[alpha_stubs[source]] = alpha_stubs[target]
                    for source_index, source in enumerate(blocks):
                        target = blocks[block_order[source_index]]
                        if flips[source_index]:
                            target = (target[1], target[0])
                        image[source[0]], image[source[1]] = target
                    permutations.append(tuple(image))
    return permutations


def transform_matching(
    vertex_count: int, matching: Matching, permutation: tuple[int, ...]
) -> Matching:
    return matching_from_edges(
        vertex_count,
        (
            (permutation[left], permutation[right])
            for left, right in matching_edges(matching)
        ),
    )


def matching_key(matching: Matching) -> tuple[Edge, ...]:
    return tuple(sorted(matching_edges(matching)))


def matching_orbit(
    vertex_count: int,
    matching: Matching,
    stabilizer: list[tuple[int, ...]],
) -> set[tuple[Edge, ...]]:
    return {
        matching_key(transform_matching(vertex_count, matching, permutation))
        for permutation in stabilizer
    }


def orbit_representatives(
    vertex_count: int,
    matchings: list[Matching],
    stabilizer: list[tuple[int, ...]],
) -> list[tuple[Matching, int]]:
    by_key = {matching_key(matching): matching for matching in matchings}
    remaining = set(by_key)
    representatives = []
    while remaining:
        key = min(remaining)
        matching = by_key[key]
        orbit = matching_orbit(vertex_count, matching, stabilizer)
        if not orbit <= set(by_key):
            raise AssertionError("the alpha stabilizer did not preserve candidates")
        representatives.append((matching, len(orbit)))
        remaining -= orbit
    return representatives


def full_graph_is_connected(vertex_count: int, matchings: tuple[Matching, ...]) -> bool:
    adjacency = [[] for _ in range(vertex_count + STUB_COUNT)]
    for matching in matchings:
        for left, right in matching_edges(matching):
            adjacency[left].append(right)
            adjacency[right].append(left)
    visited = {0}
    queue = [0]
    for vertex in queue:
        for neighbor in adjacency[vertex]:
            if neighbor not in visited:
                visited.add(neighbor)
                queue.append(neighbor)
    return len(visited) == len(adjacency)


def core_attachments_are_hole_pure(
    vertex_count: int, matchings: tuple[Matching, ...]
) -> bool:
    adjacency = [set() for _ in range(vertex_count + STUB_COUNT)]
    for matching in matchings:
        for left, right in matching_edges(matching):
            adjacency[left].add(right)
            adjacency[right].add(left)
    degrees = [len(neighbors) for neighbors in adjacency]
    in_core = [True] * len(adjacency)
    leaves = deque(
        vertex for vertex, degree in enumerate(degrees) if degree <= 1
    )
    while leaves:
        vertex = leaves.popleft()
        if not in_core[vertex]:
            continue
        in_core[vertex] = False
        for neighbor in adjacency[vertex]:
            if in_core[neighbor]:
                degrees[neighbor] -= 1
                if degrees[neighbor] == 1:
                    leaves.append(neighbor)
    core = {vertex for vertex, present in enumerate(in_core) if present}
    if not core:
        return False

    # Every component hanging from the 2-core lies wholly in one face in any
    # cellular embedding. It therefore cannot carry feet from both holes.
    visited = set(core)
    for root in core:
        for start in adjacency[root] - core:
            if start in visited:
                continue
            component = []
            queue = [start]
            visited.add(start)
            for vertex in queue:
                component.append(vertex)
                for neighbor in adjacency[vertex]:
                    if neighbor not in core and neighbor not in visited:
                        visited.add(neighbor)
                        queue.append(neighbor)
            holes = {
                (vertex - vertex_count) // 5
                for vertex in component
                if vertex >= vertex_count
            }
            if len(holes) > 1:
                return False
    return True


def trace_faces(
    vertex_count: int,
    matchings: tuple[Matching, Matching, Matching],
    orientation_mask: int,
) -> list[list[tuple[int, int]]]:
    rotations = []
    for vertex in range(vertex_count + STUB_COUNT):
        neighbors = [
            matching[vertex]
            for matching in matchings
            if matching[vertex] != -1
        ]
        if vertex < vertex_count:
            if len(neighbors) != COLOR_COUNT:
                raise AssertionError("an internal exact-system vertex is not cubic")
            if orientation_mask & (1 << vertex):
                neighbors[1], neighbors[2] = neighbors[2], neighbors[1]
        elif len(neighbors) != 1:
            raise AssertionError("an exact-system stub is not a leaf")
        rotations.append(tuple(neighbors))

    unseen = {
        dart
        for matching in matchings
        for left, right in matching_edges(matching)
        for dart in ((left, right), (right, left))
    }
    faces = []
    while unseen:
        start = min(unseen)
        dart = start
        face = []
        while True:
            unseen.remove(dart)
            face.append(dart)
            left, right = dart
            rotation = rotations[right]
            incoming = rotation.index(left)
            dart = (right, rotation[(incoming + 1) % len(rotation)])
            if dart == start:
                break
        faces.append(face)
    return faces


def is_good_inner_word(colors: list[int]) -> bool:
    if len(colors) != 5 or sorted(colors) != [0, 0, 0, 1, 2]:
        return False
    return any(
        all(colors[(start + offset) % 5] == 0 for offset in range(3))
        for start in range(5)
    )


def classify_rotation(
    vertex_count: int,
    matchings: tuple[Matching, Matching, Matching],
    orientation_mask: int,
) -> tuple[str, list[list[tuple[int, int]]]]:
    inner, outer, alpha_stubs, beta_stubs, gamma_stubs = terminal_sets(
        vertex_count
    )
    terminal_colors = {
        **{stub: 0 for stub in alpha_stubs},
        **{stub: 1 for stub in beta_stubs},
        **{stub: 2 for stub in gamma_stubs},
    }
    faces = trace_faces(vertex_count, matchings, orientation_mask)
    edge_count = (3 * vertex_count + STUB_COUNT) // 2
    expected_spherical_face_count = (
        2 - (vertex_count + STUB_COUNT) + edge_count
    )
    if len(faces) != expected_spherical_face_count:
        return "positive_genus", faces

    terminal_faces = []
    internal_faces = []
    for face in faces:
        terminals = [right for _, right in face if right >= vertex_count]
        if terminals:
            terminal_faces.append((face, terminals))
        else:
            internal_faces.append(face)
    if len(terminal_faces) != 2:
        return "wrong_hole_face_count", faces
    terminal_sets_seen = {frozenset(stubs) for _, stubs in terminal_faces}
    if terminal_sets_seen != {frozenset(inner), frozenset(outer)}:
        return "mixed_hole_feet", faces
    if any(len(face) < 5 for face in internal_faces):
        return "short_internal_face", faces

    # Restoring the five deleted cap edges subdivides each merged hole face.
    # A gap of d tangle darts becomes a face of length d + 1.
    for face, _ in terminal_faces:
        foot_positions = [
            index
            for index, (_, right) in enumerate(face)
            if right >= vertex_count
        ]
        for left, right in zip(
            foot_positions,
            foot_positions[1:] + foot_positions[:1],
            strict=True,
        ):
            gap_length = (right - left) % len(face)
            if gap_length + 1 < 5:
                return "short_cap_adjacent_face", faces
    inner_order = next(
        stubs for _, stubs in terminal_faces if set(stubs) == set(inner)
    )
    if not is_good_inner_word(
        [terminal_colors[stub] for stub in inner_order]
    ):
        return "bad_inner_word_order", faces
    return "satisfying", faces


def face_digest(faces: list[list[tuple[int, int]]]) -> str:
    payload = json.dumps(faces, separators=(",", ":"), sort_keys=True).encode()
    return hashlib.sha256(payload).hexdigest()


def audit_size(vertex_count: int) -> dict[str, object]:
    inner, outer, alpha_stubs, beta_stubs, gamma_stubs = terminal_sets(
        vertex_count
    )
    alpha = canonical_alpha_matching(vertex_count)
    beta_candidates = matching_candidates(
        vertex_count, alpha, alpha_stubs, beta_stubs
    )
    gamma_candidates = matching_candidates(
        vertex_count, alpha, alpha_stubs, gamma_stubs
    )
    stabilizer = alpha_stabilizer(vertex_count)
    if any(
        transform_matching(vertex_count, alpha, permutation) != alpha
        for permutation in stabilizer
    ):
        raise AssertionError("the declared alpha stabilizer does not fix alpha")
    beta_representatives = orbit_representatives(
        vertex_count, beta_candidates, stabilizer
    )
    orbit_sizes = [orbit_size for _, orbit_size in beta_representatives]
    if sum(orbit_sizes) != len(beta_candidates):
        raise AssertionError("the beta orbits do not partition the candidates")

    counts = {
        "representative_pair_checks": 0,
        "raw_radial_matching_triples": 0,
        "raw_connected_matching_triples": 0,
        "raw_core_attachment_eligible_matching_triples": 0,
        "representative_rotation_systems_tested": 0,
        "raw_rotation_systems_covered": 0,
        "raw_spherical_rotation_systems": 0,
        "raw_correct_hole_partition_rotation_systems": 0,
        "raw_satisfying_rotation_systems": 0,
    }
    blocker_histogram: dict[str, int] = {}
    witness = None
    expected_faces = (
        2
        - (vertex_count + STUB_COUNT)
        + (3 * vertex_count + STUB_COUNT) // 2
    )
    for beta, orbit_size in beta_representatives:
        occupied = edge_set(alpha) | edge_set(beta)
        for gamma in gamma_candidates:
            counts["representative_pair_checks"] += 1
            if occupied & edge_set(gamma):
                continue
            if not pair_is_radial_forest(
                vertex_count,
                beta,
                gamma,
                (*beta_stubs, *gamma_stubs),
            ):
                continue
            counts["raw_radial_matching_triples"] += orbit_size
            matchings = (alpha, beta, gamma)
            if not full_graph_is_connected(vertex_count, matchings):
                continue
            counts["raw_connected_matching_triples"] += orbit_size
            if expected_faces < 2:
                continue
            if not core_attachments_are_hole_pure(
                vertex_count, matchings
            ):
                continue
            counts["raw_core_attachment_eligible_matching_triples"] += orbit_size

            for reduced_mask in range(1 << (vertex_count - 1)):
                orientation_mask = reduced_mask << 1
                counts["representative_rotation_systems_tested"] += 1
                counts["raw_rotation_systems_covered"] += 2 * orbit_size
                classification, faces = classify_rotation(
                    vertex_count, matchings, orientation_mask
                )
                blocker_histogram[classification] = (
                    blocker_histogram.get(classification, 0) + 2 * orbit_size
                )
                if classification != "positive_genus":
                    counts["raw_spherical_rotation_systems"] += 2 * orbit_size
                if classification in (
                    "short_internal_face",
                    "short_cap_adjacent_face",
                    "bad_inner_word_order",
                    "satisfying",
                ):
                    counts["raw_correct_hole_partition_rotation_systems"] += (
                        2 * orbit_size
                    )
                if classification == "satisfying":
                    counts["raw_satisfying_rotation_systems"] += 2 * orbit_size
                    if witness is None:
                        witness = {
                            "alpha_edges": matching_edges(alpha),
                            "beta_edges": matching_edges(beta),
                            "gamma_edges": matching_edges(gamma),
                            "orientation_mask": orientation_mask,
                            "face_lengths": [len(face) for face in faces],
                            "face_digest": face_digest(faces),
                        }

    if sum(blocker_histogram.values()) != counts["raw_rotation_systems_covered"]:
        raise AssertionError("the rotation classifications do not conserve count")
    positive_genus_count = blocker_histogram.get("positive_genus", 0)
    if (
        counts["raw_spherical_rotation_systems"] + positive_genus_count
        != counts["raw_rotation_systems_covered"]
    ):
        raise AssertionError("the genus classification does not conserve count")
    verdict = "SAT" if counts["raw_satisfying_rotation_systems"] else "UNSAT"
    return {
        "internal_vertex_count": vertex_count,
        "inner_stub_ids": inner,
        "outer_stub_ids": outer,
        "spherical_face_count_if_connected": expected_faces,
        "alpha_stabilizer_size": len(stabilizer),
        "beta_candidate_count": len(beta_candidates),
        "gamma_candidate_count": len(gamma_candidates),
        "beta_orbit_representative_count": len(beta_representatives),
        "beta_orbit_size_histogram": {
            str(size): orbit_sizes.count(size) for size in sorted(set(orbit_sizes))
        },
        "beta_orbit_coverage_count": sum(orbit_sizes),
        **counts,
        "rotation_blocker_histogram": dict(sorted(blocker_histogram.items())),
        "witness": witness,
        "verdict": verdict,
    }


def main() -> int:
    args = parse_args()
    if any(size < 6 or size % 2 for size in args.sizes):
        raise SystemExit("all exact-system sizes must be even and at least six")
    result = {
        "schema": SCHEMA,
        "algorithm": "three-matchings-rotation-system-exhaustion-v1",
        "normalization": (
            "The six labeled alpha feet are fixed on vertices 0..5; "
            "the alpha stabilizer exhausts the remaining internal relabelings; "
            "global reversal fixes rotation bit 0."
        ),
        "conditions": [
            "simple three-edge-colored cubic internal graph",
            "ten degree-one feet, five assigned to each hole",
            "every bicolored component is a radial path",
            "two spherical face traces gather exactly one hole's feet each",
            "all non-hole faces have length at least five",
            "restoring each cap cycle creates only faces of length at least five",
            "the inner face word has cyclic block type (3,1,1)",
        ],
        "sizes": [audit_size(size) for size in args.sizes],
    }
    atomic_write_json(args.output, result)
    print(
        "; ".join(
            f"V={row['internal_vertex_count']}: {row['verdict']}"
            for row in result["sizes"]
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
