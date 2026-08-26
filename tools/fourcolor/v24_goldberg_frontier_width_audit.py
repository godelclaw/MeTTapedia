#!/usr/bin/env python3
"""Measure cap-radial frontier widths in icosahedral Goldberg fullerenes.

The source's (5,0) tube laboratory has a five-edge frontier at every bulk
level.  That symmetry must not be silently promoted to arbitrary fullerene
geometry.  This audit grows the GP(k,0) icosahedral family, measures graph
distance from one pentagonal face, and records the number of primal edges
crossing each distance ball.

The result is evidence about one natural radial decomposition, not a
counterexample to every possible corridor construction.  In particular, a
different non-radial separator or the source's two-directional construction
could still exist.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from v24_annular_census import atomic_write_json
from v24_goldberg import cap_distances, make_goldberg_graph


SCHEMA = "fourcolor-v24-goldberg-frontier-width-audit-v1"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-frequency", type=int, default=12)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_goldberg_frontier_width_audit.json"),
    )
    return parser.parse_args()


def audit_frequency(frequency: int) -> dict[str, Any]:
    graph = make_goldberg_graph(frequency)
    cap_face = graph["pentagon_face_ids"][0]
    distances = cap_distances(graph, cap_face)
    edges = [tuple(edge) for edge in graph["primal_edges"]]
    maximum_distance = max(distances)
    frontier_widths = [
        sum(
            (distances[left] <= radius) != (distances[right] <= radius)
            for left, right in edges
        )
        for radius in range(maximum_distance)
    ]
    if graph["primal_vertex_count"] != 20 * frequency * frequency:
        raise AssertionError("the Goldberg primal vertex formula failed")
    if max(frontier_widths, default=0) != 10 * frequency:
        raise AssertionError("the measured maximum frontier formula changed")
    return {
        "frequency": frequency,
        "primal_vertex_count": graph["primal_vertex_count"],
        "graph_hash": graph["graph_hash"],
        "cap_face_id": cap_face,
        "maximum_distance": maximum_distance,
        "frontier_widths": frontier_widths,
        "maximum_frontier_width": max(frontier_widths, default=0),
    }


def run(max_frequency: int) -> dict[str, Any]:
    if max_frequency < 1:
        raise ValueError("the maximum frequency must be positive")
    rows = [audit_frequency(frequency) for frequency in range(1, max_frequency + 1)]
    return {
        "schema": SCHEMA,
        "algorithm": "exact-distance-balls-and-crossing-edge-count-v1",
        "family": "icosahedral Goldberg GP(k,0)",
        "frequencies": rows,
        "observed_formula": {
            "primal_vertex_count": "20*k^2",
            "maximum_radial_frontier_width": "10*k",
        },
        "scope_warning": (
            "This rules out a constant-width cap-radial transfer on this "
            "family. It does not rule out every non-radial corridor."
        ),
    }


def main() -> int:
    args = parse_args()
    result = run(args.max_frequency)
    atomic_write_json(args.output, result)
    for row in result["frequencies"]:
        print(
            f"k={row['frequency']:2d} "
            f"V={row['primal_vertex_count']:5d} "
            f"radius={row['maximum_distance']:2d} "
            f"max_frontier={row['maximum_frontier_width']:3d}"
        )
    print(f"certificate={args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
