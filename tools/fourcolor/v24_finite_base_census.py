#!/usr/bin/env python3
"""Independent v24 census for four closed fullerenes and cap tangles."""

from __future__ import annotations

import argparse
import hashlib
import itertools
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from v24_annular_census import (
    CensusSearch,
    DIGEST_MODULUS,
    atomic_write_json,
    canonical_hash,
    dualize_triangulation,
    induced_cycle_order,
    tube_dual_triangles,
)
from v24_annular_kempe import (
    COLOR_PAIRS,
    UnionFind,
    bichromatic_components,
    is_good_word,
    switched_coloring,
)


SCHEMA = "fourcolor-v24-finite-base-census-v1"
GRAPH_NAMES = ("C20", "C24", "C30", "C40")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Reproduce the v24 closed-fullerene and cap-tangle bases."
    )
    parser.add_argument("--graph", choices=(*GRAPH_NAMES, "all"), default="all")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results/fourcolor/v24_finite_base_census"),
    )
    return parser.parse_args()


def hexagonal_barrel_dual_triangles() -> tuple[list[tuple[int, int, int]], int]:
    """Triangulated dual of the D6d C24 hexagonal barrel."""
    ring = lambda index: 2 + index % 12
    triangles = []
    for index in range(0, 12, 2):
        triangles.append(tuple(sorted((0, ring(index), ring(index + 2)))))
        triangles.append(tuple(sorted((1, ring(index + 1), ring(index + 3)))))
    for index in range(12):
        triangles.append(
            tuple(sorted((ring(index), ring(index + 1), ring(index + 2))))
        )
    triangles.sort()
    return triangles, 14


def dual_triangulation(name: str) -> tuple[list[tuple[int, int, int]], int]:
    if name == "C20":
        return tube_dual_triangles(0)
    if name == "C24":
        return hexagonal_barrel_dual_triangles()
    if name == "C30":
        return tube_dual_triangles(1)
    if name == "C40":
        return tube_dual_triangles(2)
    raise ValueError(name)


def make_incidence(
    vertex_count: int, edges: list[tuple[int, int]]
) -> list[list[int]]:
    incidence = [[] for _ in range(vertex_count)]
    for edge_index, (left, right) in enumerate(edges):
        incidence[left].append(edge_index)
        incidence[right].append(edge_index)
    return incidence


def make_graph_data(name: str) -> dict[str, Any]:
    triangles, dual_vertex_count = dual_triangulation(name)
    primal_edges, neighbors = dualize_triangulation(triangles, dual_vertex_count)
    dual_degrees = Counter(vertex for triangle in triangles for vertex in triangle)
    pentagon_points = sorted(
        vertex for vertex in range(dual_vertex_count) if dual_degrees[vertex] == 5
    )
    if len(pentagon_points) != 12:
        raise AssertionError("a fullerene base must have twelve pentagons")

    cut_point = pentagon_points[0]
    cut_vertices = {
        index for index, triangle in enumerate(triangles) if cut_point in triangle
    }
    cut_order = induced_cycle_order(cut_vertices, neighbors)
    cut_edges = {
        edge
        for edge in primal_edges
        if edge[0] in cut_vertices and edge[1] in cut_vertices
    }
    if len(cut_edges) != 5:
        raise AssertionError("the distinguished pentagon is not a five-cycle")

    graph_payload = {
        "name": name,
        "dual_vertex_count": dual_vertex_count,
        "dual_triangles": [list(triangle) for triangle in triangles],
        "primal_edges": [list(edge) for edge in primal_edges],
        "pentagon_dual_vertices": pentagon_points,
        "cut_pentagon_dual_vertex": cut_point,
        "cut_pentagon_vertices": cut_order,
        "cut_pentagon_edges": [list(edge) for edge in sorted(cut_edges)],
    }
    return {
        **graph_payload,
        "graph_hash": canonical_hash(graph_payload),
        "neighbors": neighbors,
        "cut_edges": cut_edges,
    }


def coloring_instance(graph: dict[str, Any], cap_tangle: bool) -> dict[str, Any]:
    primal_edges = [tuple(edge) for edge in graph["primal_edges"]]
    edges = [
        edge
        for edge in primal_edges
        if not cap_tangle or edge not in graph["cut_edges"]
    ]
    incidence = make_incidence(len(graph["dual_triangles"]), edges)
    spokes = []
    if cap_tangle:
        for vertex in graph["cut_pentagon_vertices"]:
            if len(incidence[vertex]) != 1:
                raise AssertionError("a cut-open cap vertex must have one spoke")
            spokes.append(incidence[vertex][0])
    elif any(len(incident) != 3 for incident in incidence):
        raise AssertionError("the closed fullerene is not cubic")

    payload = {
        "name": f"{graph['name']}-{'cap' if cap_tangle else 'closed'}",
        "base_graph_hash": graph["graph_hash"],
        "tangle_edges": [list(edge) for edge in edges],
        "outer_spokes": [],
        "inner_spokes": spokes,
    }
    return {
        **payload,
        "graph_hash": canonical_hash(payload),
        "incident_edges": incidence,
    }


def enumerate_solutions(instance: dict[str, Any]) -> tuple[list[bytes], dict[str, Any]]:
    solutions = []
    root_counts = {}
    search_nodes = 0
    dead_ends = 0
    digest_sum = 0
    digest_xor = 0
    for root_color in range(3):
        search = CensusSearch(instance, root_color, collect_solutions=True)
        search.search()
        if search.solutions is None:
            raise AssertionError("solution collection was not enabled")
        root_counts[str(root_color)] = len(search.solutions)
        search_nodes += search.search_node_count
        dead_ends += search.dead_end_count
        for coloring in search.solutions:
            digest = int.from_bytes(hashlib.sha256(coloring).digest(), "big")
            digest_sum = (digest_sum + digest) % DIGEST_MODULUS
            digest_xor ^= digest
        solutions.extend(search.solutions)
    if len(solutions) != len(set(solutions)):
        raise AssertionError("root-color shards overlap")
    return solutions, {
        "root_color_solution_counts": root_counts,
        "search_node_count": search_nodes,
        "dead_end_count": dead_ends,
        "solution_digest_sum": f"{digest_sum:064x}",
        "solution_digest_xor": f"{digest_xor:064x}",
    }


def dynamics(
    instance: dict[str, Any], solutions: list[bytes]
) -> tuple[UnionFind, int, list[int]]:
    edges = [tuple(edge) for edge in instance["tangle_edges"]]
    incidence = instance["incident_edges"]
    solution_index = {solution: index for index, solution in enumerate(solutions)}
    union_find = UnionFind(len(solutions))
    transition_edges = set()
    component_counts = []
    for source, coloring in enumerate(solutions):
        component_count = 0
        for pair in COLOR_PAIRS:
            for component in bichromatic_components(coloring, pair, edges, incidence):
                component_count += 1
                target_coloring = switched_coloring(coloring, pair, component)
                target = solution_index.get(target_coloring)
                if target is None:
                    raise AssertionError("a Kempe switch left the coloring census")
                transition_edges.add(tuple(sorted((source, target))))
                union_find.union(source, target)
        component_counts.append(component_count)
    return union_find, len(transition_edges), component_counts


def class_members(union_find: UnionFind, size: int) -> list[list[int]]:
    classes: dict[int, list[int]] = defaultdict(list)
    for member in range(size):
        classes[union_find.find(member)].append(member)
    return sorted(classes.values(), key=lambda members: (-len(members), members[0]))


def class_rows(
    classes: list[list[int]], component_counts: list[int]
) -> list[dict[str, Any]]:
    return [
        {
            "size": len(members),
            "bichromatic_component_parity_histogram": {
                str(parity): count
                for parity, count in sorted(
                    Counter(component_counts[index] % 2 for index in members).items()
                )
            },
        }
        for members in classes
    ]


def all_classes_recoloring_closed(
    solutions: list[bytes], union_find: UnionFind
) -> bool:
    solution_index = {solution: index for index, solution in enumerate(solutions)}
    for source, coloring in enumerate(solutions):
        source_root = union_find.find(source)
        for permutation in itertools.permutations(range(3)):
            recolored = bytes(permutation[color] for color in coloring)
            if union_find.find(solution_index[recolored]) != source_root:
                return False
    return True


def analyze_closed(graph: dict[str, Any]) -> dict[str, Any]:
    instance = coloring_instance(graph, cap_tangle=False)
    solutions, search = enumerate_solutions(instance)
    union_find, transition_count, component_counts = dynamics(instance, solutions)
    classes = class_members(union_find, len(solutions))
    parity_histogram = Counter(count % 2 for count in component_counts)
    return {
        "instance_hash": instance["graph_hash"],
        "solution_count": len(solutions),
        **search,
        "kempe_transition_count": transition_count,
        "kempe_class_count": len(classes),
        "kempe_class_sizes": [len(members) for members in classes],
        "bichromatic_component_parity_histogram": {
            str(parity): count for parity, count in sorted(parity_histogram.items())
        },
        "kempe_classes": class_rows(classes, component_counts),
        "all_kempe_classes_closed_under_global_recoloring": (
            all_classes_recoloring_closed(solutions, union_find)
        ),
    }


def analyze_cap(graph: dict[str, Any]) -> dict[str, Any]:
    instance = coloring_instance(graph, cap_tangle=True)
    solutions, search = enumerate_solutions(instance)
    union_find, transition_count, component_counts = dynamics(instance, solutions)
    classes = class_members(union_find, len(solutions))
    words = Counter(
        tuple(coloring[edge] for edge in instance["inner_spokes"])
        for coloring in solutions
    )
    good_count = sum(count for word, count in words.items() if is_good_word(word))
    return {
        "instance_hash": instance["graph_hash"],
        "cut_pentagon_spokes": instance["inner_spokes"],
        "solution_count": len(solutions),
        **search,
        "kempe_transition_count": transition_count,
        "kempe_class_count": len(classes),
        "kempe_class_sizes": [len(members) for members in classes],
        "inner_word_count": len(words),
        "good_word_solution_count": good_count,
        "bad_word_solution_count": len(solutions) - good_count,
        "inner_word_fiber_size_histogram": {
            str(size): count for size, count in sorted(Counter(words.values()).items())
        },
        "bichromatic_component_parity_histogram": {
            str(parity): count
            for parity, count in sorted(
                Counter(count % 2 for count in component_counts).items()
            )
        },
    }


def analyze_graph(name: str) -> dict[str, Any]:
    graph = make_graph_data(name)
    graph_fields = {
        key: value for key, value in graph.items() if key not in {"neighbors", "cut_edges"}
    }
    return {
        "schema": SCHEMA,
        "algorithm": "deterministic-mrv-and-explicit-kempe-components-v1",
        "graph": graph_fields,
        "closed": analyze_closed(graph),
        "cap_tangle": analyze_cap(graph),
    }


def main() -> int:
    args = parse_args()
    names = GRAPH_NAMES if args.graph == "all" else (args.graph,)
    for name in names:
        result = analyze_graph(name)
        output = args.output_dir / f"{name.lower()}_finite_base.json"
        atomic_write_json(output, result)
        closed = result["closed"]
        cap = result["cap_tangle"]
        print(
            f"{name}: closed {closed['solution_count']} colorings / "
            f"{closed['kempe_class_count']} classes; cap "
            f"{cap['solution_count']} colorings / {cap['kempe_class_count']} class"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
