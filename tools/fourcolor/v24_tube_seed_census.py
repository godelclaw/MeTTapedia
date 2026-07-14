#!/usr/bin/env python3
"""Resumable direct census of the v24 (5,0)-tube seed sectors."""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from pathlib import Path
from typing import Any

from v24_annular_census import (
    CensusSearch,
    DIGEST_MODULUS,
    atomic_write_json,
    canonical_hash,
    dualize_triangulation,
    induced_cycle_order,
    load_json,
    tube_dual_triangles,
)
from v24_annular_kempe import bichromatic_components
from v24_finite_base_census import make_incidence
from v24_pentagon_finite_seals import cap_cycle_extensions, component_meets_vertices


SHARD_SCHEMA = "fourcolor-v24-tube-seed-census-shard-v1"
MERGED_SCHEMA = "fourcolor-v24-tube-seed-census-v1"
CANONICAL_GOOD_WORD = (0, 0, 0, 1, 2)
MAJORITY_PAIR = (0, 1)
CATEGORIES = ("crossing", "seed_nonrouted", "seed_fully_routed")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Reproduce the v24 direct tube seed and routed counts."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--length", type=int, choices=range(1, 7))
    group.add_argument("--max-length", type=int, choices=range(1, 7), default=6)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results/fourcolor/v24_tube_seed_census"),
    )
    parser.add_argument("--force", action="store_true")
    return parser.parse_args()


def make_tube_annulus(length: int) -> dict[str, Any]:
    triangles, dual_vertex_count = tube_dual_triangles(length)
    primal_edges, neighbors = dualize_triangulation(triangles, dual_vertex_count)
    face_orders = []
    face_vertices = []
    face_edge_sets = []
    for pole in (0, 1):
        vertices = {
            index for index, triangle in enumerate(triangles) if pole in triangle
        }
        order = induced_cycle_order(vertices, neighbors)
        cycle_edges = {
            edge
            for edge in primal_edges
            if edge[0] in vertices and edge[1] in vertices
        }
        if len(vertices) != 5 or len(cycle_edges) != 5:
            raise AssertionError("a tube pole is not a pentagon")
        face_vertices.append(vertices)
        face_orders.append(order)
        face_edge_sets.append(cycle_edges)

    tangle_edges = [
        edge
        for edge in primal_edges
        if edge not in face_edge_sets[0] and edge not in face_edge_sets[1]
    ]
    incidence = make_incidence(len(triangles), tangle_edges)

    def spokes(order: list[int]) -> list[int]:
        result = []
        for vertex in order:
            if len(incidence[vertex]) != 1:
                raise AssertionError("a cut-open pole vertex must have one spoke")
            result.append(incidence[vertex][0])
        return result

    inner_cycle_edge_order = [
        tuple(
            sorted(
                (face_orders[1][index], face_orders[1][(index + 1) % 5])
            )
        )
        for index in range(5)
    ]
    if set(inner_cycle_edge_order) != face_edge_sets[1]:
        raise AssertionError("the inner face order does not trace its cycle")
    payload = {
        "name": f"C{20 + 10 * length}-tube-annulus",
        "tube_length": length,
        "dual_vertex_count": dual_vertex_count,
        "dual_triangles": [list(triangle) for triangle in triangles],
        "primal_edges": [list(edge) for edge in primal_edges],
        "outer_face_vertices": face_orders[0],
        "inner_face_vertices": face_orders[1],
        "outer_face_edges": [list(edge) for edge in sorted(face_edge_sets[0])],
        "inner_face_edges": [list(edge) for edge in inner_cycle_edge_order],
        "tangle_edges": [list(edge) for edge in tangle_edges],
        "outer_spokes": spokes(face_orders[0]),
        "inner_spokes": spokes(face_orders[1]),
    }
    return {
        **payload,
        "graph_hash": canonical_hash(payload),
        "incident_edges": incidence,
        "inner_cycle_edges": inner_cycle_edge_order,
    }


def excess_identity_audit(instance: dict[str, Any]) -> dict[str, Any]:
    """Compute the internal-face excess and the two merged hole lengths."""
    triangles = [frozenset(triangle) for triangle in instance["dual_triangles"]]
    primal_edges = [tuple(edge) for edge in instance["primal_edges"]]
    face_lengths = Counter(vertex for triangle in triangles for vertex in triangle)

    def adjacent_faces(edge: tuple[int, int]) -> frozenset[int]:
        shared = triangles[edge[0]] & triangles[edge[1]]
        if len(shared) != 2:
            raise AssertionError("a primal edge must separate two faces")
        return shared

    hole_rows = []
    hole_clusters = []
    for pole, key in ((0, "outer_face_edges"), (1, "inner_face_edges")):
        removed_edges = [tuple(edge) for edge in instance[key]]
        cluster = {pole}
        for edge in removed_edges:
            faces = adjacent_faces(edge)
            if pole not in faces:
                raise AssertionError("a removed cap edge is not incident to its pole face")
            cluster.update(faces)
        merged_boundary_length = (
            sum(face_lengths[face] for face in cluster) - 2 * len(removed_edges)
        )
        hole_clusters.append(cluster)
        hole_rows.append(
            {
                "pole_dual_vertex": pole,
                "merged_face_dual_vertices": sorted(cluster),
                "merged_boundary_walk_length": merged_boundary_length,
            }
        )

    if hole_clusters[0] & hole_clusters[1]:
        raise AssertionError("the two census hole regions overlap")
    internal_faces = sorted(
        set(range(instance["dual_vertex_count"]))
        - hole_clusters[0]
        - hole_clusters[1]
    )
    internal_lengths = [face_lengths[face] for face in internal_faces]
    internal_excess = sum(length - 6 for length in internal_lengths)
    total_hole_length = sum(
        row["merged_boundary_walk_length"] for row in hole_rows
    )
    rho = total_hole_length - 20
    return {
        "hole_regions": hole_rows,
        "total_hole_boundary_walk_length": total_hole_length,
        "rho": rho,
        "internal_face_count": len(internal_faces),
        "internal_face_length_histogram": {
            str(length): count
            for length, count in sorted(Counter(internal_lengths).items())
        },
        "internal_face_excess": internal_excess,
        "internal_face_excess_plus_rho": internal_excess + rho,
    }


def prepare_fixed_search(
    instance: dict[str, Any], root_color: int
) -> CensusSearch | None:
    search = CensusSearch(instance, root_color, collect_solutions=True)
    for edge, color in zip(
        instance["inner_spokes"], CANONICAL_GOOD_WORD, strict=True
    ):
        assigned = search.colors[edge]
        if assigned != -1:
            if assigned != color:
                return None
        elif search.domain_mask(edge) & (1 << color):
            search.assign(edge, color)
        else:
            return None
    return search


def category_digest(
    coloring: bytes, digest_sum: int, digest_xor: int
) -> tuple[int, int]:
    digest = int.from_bytes(hashlib.sha256(coloring).digest(), "big")
    return (digest_sum + digest) % DIGEST_MODULUS, digest_xor ^ digest


def classify_coloring(instance: dict[str, Any], coloring: bytes) -> str:
    edges = [tuple(edge) for edge in instance["tangle_edges"]]
    inner_spokes = frozenset(instance["inner_spokes"])
    outer_spokes = frozenset(instance["outer_spokes"])
    components = list(
        bichromatic_components(
            coloring, MAJORITY_PAIR, edges, instance["incident_edges"]
        )
    )
    routed_inner_spokes = frozenset().union(
        *(
            component & inner_spokes
            for component in components
            if not component.isdisjoint(outer_spokes)
        )
    )
    active_inner_spokes = frozenset(
        edge
        for edge, color in zip(
            instance["inner_spokes"], CANONICAL_GOOD_WORD, strict=True
        )
        if color in MAJORITY_PAIR
    )
    fully_routed = routed_inner_spokes == active_inner_spokes

    cycle_colors = cap_cycle_extensions(CANONICAL_GOOD_WORD)
    if len(cycle_colors) != 1:
        raise AssertionError("the canonical good word must extend uniquely")
    extended_edges = edges + list(instance["inner_cycle_edges"])
    extended_incidence = make_incidence(
        len(instance["dual_triangles"]), extended_edges
    )
    extended_coloring = coloring + bytes(cycle_colors[0])
    cap_vertices = frozenset(instance["inner_face_vertices"])
    cap_component_count = sum(
        component_meets_vertices(component, extended_edges, cap_vertices)
        for component in bichromatic_components(
            extended_coloring,
            MAJORITY_PAIR,
            extended_edges,
            extended_incidence,
        )
    )
    menu_b = cap_component_count >= 2
    if fully_routed and not menu_b:
        raise AssertionError("a fully routed state must be a parallel seed")
    if not menu_b:
        return "crossing"
    return "seed_fully_routed" if fully_routed else "seed_nonrouted"


def shard_path(output_dir: Path, length: int, root_color: int) -> Path:
    return output_dir / f"tube_j{length}_root_color_{root_color}.json"


def shard_is_reusable(
    certificate: dict[str, Any], instance: dict[str, Any], root_color: int
) -> bool:
    histogram = certificate.get("category_histogram")
    return (
        certificate.get("schema") == SHARD_SCHEMA
        and certificate.get("algorithm")
        == "fixed-inner-word-deterministic-mrv-v1"
        and certificate.get("graph_hash") == instance["graph_hash"]
        and certificate.get("tube_length") == instance["tube_length"]
        and certificate.get("fixed_inner_word") == "".join(
            map(str, CANONICAL_GOOD_WORD)
        )
        and certificate.get("majority_pair") == "".join(map(str, MAJORITY_PAIR))
        and certificate.get("root_edge_index") == 0
        and certificate.get("root_color") == root_color
        and isinstance(histogram, dict)
        and set(histogram) == set(CATEGORIES)
        and sum(int(count) for count in histogram.values())
        == certificate.get("solution_count")
    )


def run_shard(
    instance: dict[str, Any], root_color: int, output_dir: Path, force: bool
) -> dict[str, Any]:
    path = shard_path(output_dir, instance["tube_length"], root_color)
    if path.exists() and not force:
        existing = load_json(path)
        if shard_is_reusable(existing, instance, root_color):
            return existing

    search = prepare_fixed_search(instance, root_color)
    if search is None:
        solutions = []
        search_nodes = 0
        dead_ends = 0
    else:
        search.search()
        if search.solutions is None:
            raise AssertionError("solution collection was not enabled")
        solutions = search.solutions
        search_nodes = search.search_node_count
        dead_ends = search.dead_end_count

    histogram = Counter({category: 0 for category in CATEGORIES})
    digest_sums = {category: 0 for category in CATEGORIES}
    digest_xors = {category: 0 for category in CATEGORIES}
    for coloring in solutions:
        category = classify_coloring(instance, coloring)
        histogram[category] += 1
        digest_sums[category], digest_xors[category] = category_digest(
            coloring, digest_sums[category], digest_xors[category]
        )
    certificate = {
        "schema": SHARD_SCHEMA,
        "algorithm": "fixed-inner-word-deterministic-mrv-v1",
        "graph_hash": instance["graph_hash"],
        "tube_length": instance["tube_length"],
        "fixed_inner_word": "".join(map(str, CANONICAL_GOOD_WORD)),
        "majority_pair": "".join(map(str, MAJORITY_PAIR)),
        "root_edge_index": 0,
        "root_edge": instance["tangle_edges"][0],
        "root_color": root_color,
        "solution_count": len(solutions),
        "search_node_count": search_nodes,
        "dead_end_count": dead_ends,
        "category_histogram": dict(sorted(histogram.items())),
        "category_digest_sum": {
            category: f"{digest_sums[category]:064x}" for category in CATEGORIES
        },
        "category_digest_xor": {
            category: f"{digest_xors[category]:064x}" for category in CATEGORIES
        },
    }
    atomic_write_json(path, certificate)
    return certificate


def merge_shards(
    instance: dict[str, Any], shards: list[dict[str, Any]]
) -> dict[str, Any]:
    if any(
        not shard_is_reusable(shard, instance, root_color)
        for root_color, shard in enumerate(shards)
    ):
        raise ValueError("a tube seed shard does not match its graph")
    histogram = Counter({category: 0 for category in CATEGORIES})
    digest_sums = {category: 0 for category in CATEGORIES}
    digest_xors = {category: 0 for category in CATEGORIES}
    for shard in shards:
        histogram.update(shard["category_histogram"])
        for category in CATEGORIES:
            digest_sums[category] = (
                digest_sums[category]
                + int(shard["category_digest_sum"][category], 16)
            ) % DIGEST_MODULUS
            digest_xors[category] ^= int(
                shard["category_digest_xor"][category], 16
            )
    graph_fields = {
        key: value
        for key, value in instance.items()
        if key not in {"incident_edges", "inner_cycle_edges"}
    }
    return {
        "schema": MERGED_SCHEMA,
        "algorithm": "fixed-inner-word-deterministic-mrv-v1",
        "graph": graph_fields,
        "fixed_inner_word": "".join(map(str, CANONICAL_GOOD_WORD)),
        "majority_pair": "".join(map(str, MAJORITY_PAIR)),
        "root_color_solution_counts": {
            str(root_color): shard["solution_count"]
            for root_color, shard in enumerate(shards)
        },
        "solution_count": sum(shard["solution_count"] for shard in shards),
        "search_node_count": sum(shard["search_node_count"] for shard in shards),
        "dead_end_count": sum(shard["dead_end_count"] for shard in shards),
        "category_histogram": dict(sorted(histogram.items())),
        "seed_count": histogram["seed_nonrouted"]
        + histogram["seed_fully_routed"],
        "fully_routed_seed_count": histogram["seed_fully_routed"],
        "excess_identity": excess_identity_audit(instance),
        "category_digest_sum": {
            category: f"{digest_sums[category]:064x}" for category in CATEGORIES
        },
        "category_digest_xor": {
            category: f"{digest_xors[category]:064x}" for category in CATEGORIES
        },
        "shard_files": [
            shard_path(Path("."), instance["tube_length"], root_color).name
            for root_color in range(3)
        ],
    }


def run_length(length: int, output_dir: Path, force: bool) -> dict[str, Any]:
    instance = make_tube_annulus(length)
    shards = [
        run_shard(instance, root_color, output_dir, force)
        for root_color in range(3)
    ]
    result = merge_shards(instance, shards)
    output = output_dir / f"tube_j{length}_seed_census.json"
    atomic_write_json(output, result)
    print(
        f"j={length}: {result['solution_count']} fixed-word colorings; "
        f"seeds {result['seed_count']}; fully routed "
        f"{result['fully_routed_seed_count']}"
    )
    return result


def main() -> int:
    args = parse_args()
    lengths = (
        (args.length,)
        if args.length is not None
        else tuple(range(1, args.max_length + 1))
    )
    for length in lengths:
        run_length(length, args.output_dir, args.force)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
