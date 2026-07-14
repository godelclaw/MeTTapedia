#!/usr/bin/env python3
"""Independent finite audits for the v24 pentagon machinery."""

from __future__ import annotations

import argparse
import itertools
from collections import Counter
from pathlib import Path
from typing import Any

from v24_annular_census import atomic_write_json, canonical_hash, induced_cycle_order
from v24_annular_kempe import (
    COLOR_PAIRS,
    bichromatic_components,
    is_good_word,
    switched_coloring,
)
from v24_closed_web import closed_web_anatomy
from v24_finite_base_census import (
    coloring_instance,
    enumerate_solutions,
    make_graph_data,
    make_incidence,
)


SCHEMA = "fourcolor-v24-pentagon-finite-seals-v1"
GRAPH_NAMES = ("C24", "C30", "C40")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Reproduce v24 rotor, menu-B, and propagation audits."
    )
    parser.add_argument("--graph", choices=(*GRAPH_NAMES, "all"), default="all")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results/fourcolor/v24_pentagon_finite_seals"),
    )
    return parser.parse_args()


def face_vertices(graph: dict[str, Any], dual_vertex: int) -> set[int]:
    return {
        index
        for index, triangle in enumerate(graph["dual_triangles"])
        if dual_vertex in triangle
    }


def first_disjoint_pentagon_pair(graph: dict[str, Any]) -> tuple[int, int]:
    for outer, inner in itertools.combinations(graph["pentagon_dual_vertices"], 2):
        if face_vertices(graph, outer).isdisjoint(face_vertices(graph, inner)):
            return outer, inner
    raise AssertionError("the fullerene has no vertex-disjoint pentagons")


def make_annular_data(name: str) -> dict[str, Any]:
    graph = make_graph_data(name)
    outer_dual, inner_dual = first_disjoint_pentagon_pair(graph)
    outer_vertices = face_vertices(graph, outer_dual)
    inner_vertices = face_vertices(graph, inner_dual)
    outer_order = induced_cycle_order(outer_vertices, graph["neighbors"])
    inner_order = induced_cycle_order(inner_vertices, graph["neighbors"])
    primal_edges = [tuple(edge) for edge in graph["primal_edges"]]

    def cycle_edges(vertices: set[int]) -> set[tuple[int, int]]:
        return {
            edge
            for edge in primal_edges
            if edge[0] in vertices and edge[1] in vertices
        }

    outer_cycle_edges = cycle_edges(outer_vertices)
    inner_cycle_edges = cycle_edges(inner_vertices)
    if len(outer_cycle_edges) != 5 or len(inner_cycle_edges) != 5:
        raise AssertionError("both annular holes must be pentagons")
    tangle_edges = [
        edge
        for edge in primal_edges
        if edge not in outer_cycle_edges and edge not in inner_cycle_edges
    ]
    incidence = make_incidence(len(graph["dual_triangles"]), tangle_edges)

    def spokes(order: list[int]) -> list[int]:
        result = []
        for vertex in order:
            if len(incidence[vertex]) != 1:
                raise AssertionError("a cut-open pentagon vertex must have one spoke")
            result.append(incidence[vertex][0])
        return result

    outer_cycle_edge_order = [
        tuple(sorted((outer_order[index], outer_order[(index + 1) % 5])))
        for index in range(5)
    ]
    inner_cycle_edge_order = [
        tuple(sorted((inner_order[index], inner_order[(index + 1) % 5])))
        for index in range(5)
    ]
    if set(outer_cycle_edge_order) != outer_cycle_edges:
        raise AssertionError("outer face order does not trace its cycle")
    if set(inner_cycle_edge_order) != inner_cycle_edges:
        raise AssertionError("inner face order does not trace its cycle")
    payload = {
        "name": f"{name}-first-disjoint-pentagons",
        "base_graph_hash": graph["graph_hash"],
        "pentagon_pair_selection": "lexicographically-first-vertex-disjoint",
        "outer_pentagon_dual_vertex": outer_dual,
        "inner_pentagon_dual_vertex": inner_dual,
        "outer_face_vertices": outer_order,
        "inner_face_vertices": inner_order,
        "outer_face_edges": [list(edge) for edge in outer_cycle_edge_order],
        "inner_face_edges": [list(edge) for edge in inner_cycle_edge_order],
        "tangle_edges": [list(edge) for edge in tangle_edges],
        "outer_spokes": spokes(outer_order),
        "inner_spokes": spokes(inner_order),
    }
    return {
        **payload,
        "graph_hash": canonical_hash(payload),
        "incident_edges": incidence,
        "base_graph": graph,
        "inner_cycle_edges": inner_cycle_edge_order,
    }


def cap_cycle_extensions(word: tuple[int, ...]) -> list[tuple[int, ...]]:
    """Color the cycle edge i--i+1 compatibly with the five spoke colors."""
    extensions = []
    for cycle_colors in itertools.product(range(3), repeat=5):
        if all(
            {word[index], cycle_colors[index - 1], cycle_colors[index]}
            == {0, 1, 2}
            for index in range(5)
        ):
            extensions.append(cycle_colors)
    return extensions


def cap_pairing(
    word: tuple[int, ...],
    cycle_colors: tuple[int, ...],
    pair: tuple[int, int],
) -> tuple[tuple[int, int], ...]:
    """Pair the active spokes through the restored pentagon cycle."""
    active = {index for index, color in enumerate(word) if color in pair}
    unseen = set(range(5))
    paired = []
    while unseen:
        first = min(unseen)
        component = {first}
        stack = [first]
        unseen.remove(first)
        while stack:
            vertex = stack.pop()
            for edge_index, neighbor in (
                ((vertex - 1) % 5, (vertex - 1) % 5),
                (vertex, (vertex + 1) % 5),
            ):
                if cycle_colors[edge_index] in pair and neighbor in unseen:
                    unseen.remove(neighbor)
                    component.add(neighbor)
                    stack.append(neighbor)
        terminals = sorted(component & active)
        if terminals:
            if len(terminals) != 2:
                raise AssertionError("a cap path must pair two active spokes")
            paired.append(tuple(terminals))
    return tuple(sorted(paired))


def majority_pairs(word: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    counts = Counter(word)
    majority = max(counts, key=counts.get)
    return tuple(
        sorted(tuple(sorted((majority, other))) for other in range(3) if other != majority)
    )


def cyclic_distance(left: int, right: int) -> int:
    distance = abs(left - right)
    return min(distance, 5 - distance)


def rotor_and_pairing_invariance_audit() -> dict[str, Any]:
    words = [
        word
        for word in itertools.product(range(3), repeat=5)
        if is_good_word(word)
    ]
    rows = []
    invariance_checks = 0
    failures = []
    for word in words:
        extensions = cap_cycle_extensions(word)
        if len(extensions) != 1:
            raise AssertionError("a good word must have one cap extension")
        cycle_colors = extensions[0]
        pairing_rows = []
        for pair in majority_pairs(word):
            pairing = cap_pairing(word, cycle_colors, pair)
            distance_type = sorted(
                cyclic_distance(left, right) for left, right in pairing
            )
            pairing_rows.append(
                {
                    "color_pair": "".join(map(str, pair)),
                    "pairing": [list(block) for block in pairing],
                    "cyclic_distance_type": distance_type,
                }
            )
            for block in pairing:
                flipped = list(word)
                left_color, right_color = pair
                for position in block:
                    flipped[position] = (
                        right_color
                        if flipped[position] == left_color
                        else left_color
                    )
                flipped_word = tuple(flipped)
                flipped_extensions = cap_cycle_extensions(flipped_word)
                passed = (
                    is_good_word(flipped_word)
                    and len(flipped_extensions) == 1
                    and cap_pairing(flipped_word, flipped_extensions[0], pair) == pairing
                )
                invariance_checks += 1
                if not passed:
                    failures.append(
                        {
                            "word": "".join(map(str, word)),
                            "color_pair": "".join(map(str, pair)),
                            "flipped_positions": list(block),
                        }
                    )
        rows.append(
            {
                "word": "".join(map(str, word)),
                "cap_cycle_colors": "".join(map(str, cycle_colors)),
                "majority_pairings": pairing_rows,
            }
        )
    return {
        "good_word_count": len(words),
        "all_majority_pairings_have_weave_distance_type_1_2": all(
            pairing["cyclic_distance_type"] == [1, 2]
            for row in rows
            for pairing in row["majority_pairings"]
        ),
        "pairing_invariance_check_count": invariance_checks,
        "pairing_invariance_failure_count": len(failures),
        "pairing_invariance_failures": failures,
        "rotor_rows": rows,
    }


def cap_composed_data(
    annulus: dict[str, Any], coloring: bytes
) -> tuple[bytes, list[tuple[int, int]], list[list[int]]]:
    word = tuple(coloring[edge] for edge in annulus["inner_spokes"])
    extensions = cap_cycle_extensions(word)
    if len(extensions) != 1:
        raise AssertionError("the annular state does not extend uniquely over the cap")

    tangle_edges = [tuple(edge) for edge in annulus["tangle_edges"]]
    inner_cycle_edges = list(annulus["inner_cycle_edges"])
    extended_edges = tangle_edges + inner_cycle_edges
    extended_incidence = make_incidence(
        len(annulus["base_graph"]["dual_triangles"]), extended_edges
    )
    edge_color = dict(zip(inner_cycle_edges, extensions[0], strict=True))
    extended_coloring = coloring + bytes(edge_color[edge] for edge in inner_cycle_edges)
    return extended_coloring, extended_edges, extended_incidence


def component_meets_vertices(
    component: frozenset[int],
    edges: list[tuple[int, int]],
    vertices: frozenset[int],
) -> bool:
    return any(
        edges[edge][0] in vertices or edges[edge][1] in vertices
        for edge in component
    )


def menu_b_pairs(
    annulus: dict[str, Any], coloring: bytes
) -> tuple[tuple[int, int], ...]:
    word = tuple(coloring[edge] for edge in annulus["inner_spokes"])
    extended_coloring, extended_edges, extended_incidence = cap_composed_data(
        annulus, coloring
    )
    cap_vertices = frozenset(annulus["inner_face_vertices"])
    result = []
    for pair in majority_pairs(word):
        meeting_count = sum(
            component_meets_vertices(component, extended_edges, cap_vertices)
            for component in bichromatic_components(
                extended_coloring, pair, extended_edges, extended_incidence
            )
        )
        if meeting_count >= 2:
            result.append(pair)
    return tuple(result)


def propagation_audit(
    annulus: dict[str, Any], good_solutions: list[bytes]
) -> dict[str, Any]:
    good_solution_index = {solution: index for index, solution in enumerate(good_solutions)}
    menu_pairs = {solution: menu_b_pairs(annulus, solution) for solution in good_solutions}
    cap_vertices = frozenset(annulus["inner_face_vertices"])
    checked = 0
    preserved = 0
    target_missing = 0
    target_cap_reconstruction_mismatch = 0
    for source in good_solutions:
        extended, edges, incidence = cap_composed_data(annulus, source)
        tangle_edge_count = len(annulus["tangle_edges"])
        for pair in menu_pairs[source]:
            for component in bichromatic_components(extended, pair, edges, incidence):
                if not component_meets_vertices(component, edges, cap_vertices):
                    continue
                checked += 1
                switched = switched_coloring(extended, pair, component)
                target = switched[:tangle_edge_count]
                if target not in good_solution_index:
                    target_missing += 1
                    continue
                reconstructed, _, _ = cap_composed_data(annulus, target)
                if reconstructed != switched:
                    target_cap_reconstruction_mismatch += 1
                    continue
                if pair in menu_pairs[target]:
                    preserved += 1
    return {
        "cap_composed_menu_b_move_count": checked,
        "target_good_state_missing_count": target_missing,
        "target_cap_reconstruction_mismatch_count": (
            target_cap_reconstruction_mismatch
        ),
        "menu_b_preserved_move_count": preserved,
        "all_cap_composed_menu_b_moves_preserve_menu_b": (
            checked == preserved
            and target_missing == 0
            and target_cap_reconstruction_mismatch == 0
        ),
    }


def annular_audit(name: str) -> dict[str, Any]:
    annulus = make_annular_data(name)
    solutions, search = enumerate_solutions(annulus)
    inner_spoke_order = annulus["inner_spokes"]
    good_solutions = [
        coloring
        for coloring in solutions
        if is_good_word(tuple(coloring[edge] for edge in inner_spoke_order))
    ]
    fibers: dict[tuple[int, ...], list[bytes]] = {}
    for coloring in good_solutions:
        word = tuple(coloring[edge] for edge in inner_spoke_order)
        fibers.setdefault(word, []).append(coloring)
    pair_count_histogram = Counter()
    menu_b_by_word = {}
    menu_b_state_count = 0
    good_closed_web_count = 0
    tangle_edges = [tuple(edge) for edge in annulus["tangle_edges"]]
    inner_spokes = frozenset(annulus["inner_spokes"])
    outer_spokes = frozenset(annulus["outer_spokes"])
    for word, members in fibers.items():
        seeded = 0
        for coloring in members:
            pair_count = len(menu_b_pairs(annulus, coloring))
            pair_count_histogram[pair_count] += 1
            if pair_count > 0:
                seeded += 1
                menu_b_state_count += 1
            if (
                closed_web_anatomy(
                    coloring,
                    tangle_edges,
                    annulus["incident_edges"],
                    inner_spokes,
                    outer_spokes,
                )
                is not None
            ):
                good_closed_web_count += 1
        menu_b_by_word[word] = seeded

    annulus_fields = {
        key: value
        for key, value in annulus.items()
        if key not in {"incident_edges", "base_graph", "inner_cycle_edges"}
    }
    return {
        "annulus": annulus_fields,
        "solution_count": len(solutions),
        **search,
        "good_word_solution_count": len(good_solutions),
        "good_inner_word_fiber_count": len(fibers),
        "good_fiber_size_histogram": {
            str(size): count
            for size, count in sorted(Counter(map(len, fibers.values())).items())
        },
        "menu_b_state_count": menu_b_state_count,
        "menu_a_only_state_count": len(good_solutions) - menu_b_state_count,
        "menu_b_pair_count_per_state_histogram": {
            str(count): states
            for count, states in sorted(pair_count_histogram.items())
        },
        "menu_b_pair_instance_count": sum(
            pair_count * state_count
            for pair_count, state_count in pair_count_histogram.items()
        ),
        "fibers_containing_menu_b_count": sum(
            count > 0 for count in menu_b_by_word.values()
        ),
        "all_good_fibers_contain_menu_b": all(
            count > 0 for count in menu_b_by_word.values()
        ),
        "good_word_closed_web_count": good_closed_web_count,
        "good_fibers": [
            {
                "inner_word": "".join(map(str, word)),
                "fiber_size": len(fibers[word]),
                "menu_b_state_count": menu_b_by_word[word],
            }
            for word in sorted(fibers)
        ],
        "propagation": propagation_audit(annulus, good_solutions),
    }


def closed_cap_configuration_audit(name: str) -> dict[str, Any]:
    graph = make_graph_data(name)
    instance = coloring_instance(graph, cap_tangle=False)
    solutions, _ = enumerate_solutions(instance)
    edges = [tuple(edge) for edge in instance["tangle_edges"]]
    incidence = instance["incident_edges"]
    component_cache = [
        {
            pair: list(bichromatic_components(coloring, pair, edges, incidence))
            for pair in COLOR_PAIRS
        }
        for coloring in solutions
    ]
    histogram = Counter()
    good_instance_count = 0
    for dual_vertex in graph["pentagon_dual_vertices"]:
        vertices = face_vertices(graph, dual_vertex)
        order = induced_cycle_order(vertices, graph["neighbors"])
        spokes = []
        for vertex in order:
            external = [
                edge_index
                for edge_index in incidence[vertex]
                if not (
                    edges[edge_index][0] in vertices
                    and edges[edge_index][1] in vertices
                )
            ]
            if len(external) != 1:
                raise AssertionError("a pentagon vertex must have one external edge")
            spokes.append(external[0])
        cap_vertices = frozenset(vertices)
        for coloring, components in zip(solutions, component_cache, strict=True):
            word = tuple(coloring[edge] for edge in spokes)
            if not is_good_word(word):
                continue
            good_instance_count += 1
            meeting_counts = []
            for pair in majority_pairs(word):
                meeting_counts.append(
                    sum(
                        component_meets_vertices(component, edges, cap_vertices)
                        for component in components[pair]
                    )
                )
            histogram[tuple(sorted(meeting_counts))] += 1
    return {
        "closed_coloring_count": len(solutions),
        "pentagon_count": len(graph["pentagon_dual_vertices"]),
        "good_coloring_pentagon_instance_count": good_instance_count,
        "all_closed_coloring_pentagon_words_good": (
            good_instance_count
            == len(solutions) * len(graph["pentagon_dual_vertices"])
        ),
        "majority_pair_component_count_histogram": {
            ",".join(map(str, counts)): count
            for counts, count in sorted(histogram.items())
        },
        "both_majority_pairs_single_component_count": histogram[(1, 1)],
    }


def analyze_graph(name: str) -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "algorithm": "restored-cap-components-and-exhaustive-colorings-v1",
        "graph": name,
        "annular": annular_audit(name),
        "closed_cap_configurations": closed_cap_configuration_audit(name),
    }


def main() -> int:
    args = parse_args()
    names = GRAPH_NAMES if args.graph == "all" else (args.graph,)
    rotor = rotor_and_pairing_invariance_audit()
    atomic_write_json(args.output_dir / "rotor_and_pairing_invariance.json", rotor)
    print(
        f"rotor: {rotor['good_word_count']} words; pairing invariance "
        f"{rotor['pairing_invariance_check_count'] - rotor['pairing_invariance_failure_count']}"
        f"/{rotor['pairing_invariance_check_count']}"
    )
    for name in names:
        result = analyze_graph(name)
        output = args.output_dir / f"{name.lower()}_pentagon_finite_seals.json"
        atomic_write_json(output, result)
        annular = result["annular"]
        propagation = annular["propagation"]
        print(
            f"{name}: menu-B {annular['menu_b_state_count']}/"
            f"{annular['good_word_solution_count']}; propagation "
            f"{propagation['menu_b_preserved_move_count']}/"
            f"{propagation['cap_composed_menu_b_move_count']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
