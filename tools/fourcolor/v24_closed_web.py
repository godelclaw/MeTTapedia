#!/usr/bin/env python3
"""Independent closed-web analysis for the v24 annular census tangles.

For each proper Tait coloring, a bichromatic component is inner-touching
when it contains an inner boundary spoke.  The web is the union of those
components.  It is totally closed exactly when the two bichromatic
components containing each web edge are both inner-touching.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from pathlib import Path
from typing import Any

from v24_annular_census import (
    DIGEST_MODULUS,
    atomic_write_json,
    make_instance,
)
from v24_annular_kempe import (
    COLOR_PAIRS,
    bichromatic_components,
    enumerate_solutions,
    is_good_word,
)


SCHEMA = "fourcolor-v24-annular-closed-web-census-v1"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Reproduce the v24 C30/C40 totally closed-web counts."
    )
    parser.add_argument(
        "--graph", choices=("C30", "C40", "all"), default="all"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results/fourcolor/v24_annular_census"),
    )
    return parser.parse_args()


def word_text(word: tuple[int, ...]) -> str:
    return "".join(map(str, word))


def count_type(word: tuple[int, ...]) -> str:
    return ",".join(map(str, sorted(Counter(word).values(), reverse=True)))


def component_data(
    coloring: bytes,
    edges: list[tuple[int, int]],
    incident_edges: list[list[int]],
    inner_spokes: frozenset[int],
    outer_spokes: frozenset[int],
) -> tuple[
    dict[tuple[tuple[int, int], int], int],
    dict[int, bool],
    dict[int, tuple[int, int]],
]:
    """Index each bichromatic component and record its boundary ends."""
    component_at: dict[tuple[tuple[int, int], int], int] = {}
    inner_touching: dict[int, bool] = {}
    boundary_ends: dict[int, tuple[int, int]] = {}
    component_id = 0
    for pair in COLOR_PAIRS:
        for component in bichromatic_components(
            coloring, pair, edges, incident_edges
        ):
            inner_count = len(component & inner_spokes)
            outer_count = len(component & outer_spokes)
            inner_touching[component_id] = inner_count > 0
            boundary_ends[component_id] = (inner_count, outer_count)
            for edge_index in component:
                component_at[(pair, edge_index)] = component_id
            component_id += 1
    return component_at, inner_touching, boundary_ends


def closed_web_anatomy(
    coloring: bytes,
    edges: list[tuple[int, int]],
    incident_edges: list[list[int]],
    inner_spokes: frozenset[int],
    outer_spokes: frozenset[int],
) -> tuple[tuple[int, int, int], int] | None:
    """Return the anatomy and legal-component count, or None if not closed."""
    component_at, inner_touching, boundary_ends = component_data(
        coloring, edges, incident_edges, inner_spokes, outer_spokes
    )

    for edge_index, color in enumerate(coloring):
        containing = [
            component_at[(pair, edge_index)]
            for pair in COLOR_PAIRS
            if color in pair
        ]
        if len(containing) != 2:
            raise AssertionError("an edge must lie in two bichromatic components")
        statuses = {inner_touching[component_id] for component_id in containing}
        if len(statuses) != 1:
            return None

    web_components = {
        component_at[(pair, edge_index)]
        for edge_index in inner_spokes
        for pair in COLOR_PAIRS
        if coloring[edge_index] in pair
    }
    anatomy = Counter(boundary_ends[component_id] for component_id in web_components)
    unexpected = set(anatomy) - {(2, 0), (1, 1), (0, 2)}
    if unexpected:
        raise AssertionError(f"a web component has unexpected boundary ends: {unexpected}")
    result = anatomy[(2, 0)], anatomy[(1, 1)], anatomy[(0, 2)]
    inner_avoiding_count = sum(not status for status in inner_touching.values())
    return result, inner_avoiding_count


def add_digest(
    coloring: bytes, digest_sum: int, digest_xor: int
) -> tuple[int, int]:
    digest = int.from_bytes(hashlib.sha256(coloring).digest(), "big")
    return (digest_sum + digest) % DIGEST_MODULUS, digest_xor ^ digest


def analyze_graph(name: str) -> dict[str, Any]:
    instance = make_instance(name)
    edges = [tuple(edge) for edge in instance["tangle_edges"]]
    incident_edges = instance["incident_edges"]
    inner_spoke_order = tuple(instance["inner_spokes"])
    inner_spokes = frozenset(inner_spoke_order)
    outer_spokes = frozenset(instance["outer_spokes"])
    solutions = enumerate_solutions(instance)

    fiber_sizes: Counter[tuple[int, ...]] = Counter(
        tuple(coloring[edge] for edge in inner_spoke_order) for coloring in solutions
    )
    closed_by_word: Counter[tuple[int, ...]] = Counter()
    anatomy_histogram: Counter[tuple[int, int, int]] = Counter()
    closed_web_count_type_histogram: Counter[str] = Counter()
    inner_avoiding_component_histogram: Counter[int] = Counter()
    closed_digest_sum = 0
    closed_digest_xor = 0
    good_closed_count = 0

    for coloring in solutions:
        analysis = closed_web_anatomy(
            coloring, edges, incident_edges, inner_spokes, outer_spokes
        )
        if analysis is None:
            continue
        anatomy, inner_avoiding_count = analysis
        word = tuple(coloring[edge] for edge in inner_spoke_order)
        closed_by_word[word] += 1
        anatomy_histogram[anatomy] += 1
        closed_web_count_type_histogram[count_type(word)] += 1
        inner_avoiding_component_histogram[inner_avoiding_count] += 1
        good_closed_count += int(is_good_word(word))
        closed_digest_sum, closed_digest_xor = add_digest(
            coloring, closed_digest_sum, closed_digest_xor
        )

    word_rows = []
    for word, closed_count in sorted(closed_by_word.items()):
        word_rows.append(
            {
                "inner_word": word_text(word),
                "count_type": count_type(word),
                "fiber_size": fiber_sizes[word],
                "closed_web_count": closed_count,
                "entire_fiber_closed": closed_count == fiber_sizes[word],
            }
        )

    total_closed = sum(closed_by_word.values())
    closed_fiber_size_histogram = Counter(row["fiber_size"] for row in word_rows)
    closed_per_word_histogram = Counter(
        row["closed_web_count"] for row in word_rows
    )
    closed_inner_word_count_type_histogram = Counter(
        row["count_type"] for row in word_rows
    )
    return {
        "schema": SCHEMA,
        "algorithm": "explicit-bichromatic-inner-touching-components-v1",
        "graph": name,
        "graph_hash": instance["graph_hash"],
        "solution_count": len(solutions),
        "totally_closed_web_count": total_closed,
        "good_word_closed_web_count": good_closed_count,
        "bad_word_closed_web_count": total_closed - good_closed_count,
        "closed_inner_word_count": len(closed_by_word),
        "closed_inner_word_count_type_histogram": dict(
            sorted(closed_inner_word_count_type_histogram.items())
        ),
        "closed_web_count_type_histogram": dict(
            sorted(closed_web_count_type_histogram.items())
        ),
        "closed_web_anatomy_histogram": {
            ",".join(map(str, anatomy)): count
            for anatomy, count in sorted(anatomy_histogram.items())
        },
        "closed_fiber_size_histogram": {
            str(size): count
            for size, count in sorted(closed_fiber_size_histogram.items())
        },
        "closed_webs_per_inner_word_histogram": {
            str(size): count
            for size, count in sorted(closed_per_word_histogram.items())
        },
        "closed_state_inner_avoiding_component_count_histogram": {
            str(size): count
            for size, count in sorted(inner_avoiding_component_histogram.items())
        },
        "all_closed_words_have_entire_fiber_closed": all(
            row["entire_fiber_closed"] for row in word_rows
        ),
        "closed_solution_digest_sum": f"{closed_digest_sum:064x}",
        "closed_solution_digest_xor": f"{closed_digest_xor:064x}",
        "closed_inner_word_fibers": word_rows,
    }


def main() -> int:
    args = parse_args()
    names = ("C30", "C40") if args.graph == "all" else (args.graph,)
    for name in names:
        result = analyze_graph(name)
        output = args.output_dir / f"{name.lower()}_annular_closed_web.json"
        atomic_write_json(output, result)
        print(
            f"{name}: {result['totally_closed_web_count']} closed webs, "
            f"{result['good_word_closed_web_count']} at good words, "
            f"{result['closed_inner_word_count']} closed fibers"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
