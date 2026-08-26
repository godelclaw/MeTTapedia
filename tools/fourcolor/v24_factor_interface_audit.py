#!/usr/bin/env python3
"""Audit a tempting but invalid factor-interface strengthening.

The v24 framed move relation permits a two-colour component switch only when
the component avoids every frozen boundary edge.  This script uses the source
C30 polar annulus, deletes one deterministic interior edge to create two
defects, and compares completion reachability when neither, either, or both
five-edge annular boundaries are frozen.

This is a regression test for proof design, not a counterexample to Trail
Completability: an arbitrary twice-frozen annular tangle need not be a source
trail factor.  Its purpose is narrower.  It shows that factor independence
cannot be obtained merely by freezing every seam; the geometry of the actual
factorization or an exact synchronized finite-state argument is necessary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import deque
from pathlib import Path
from typing import Any

from v24_annular_census import atomic_write_json, make_instance
from v24_annular_kempe import (
    COLOR_PAIRS,
    bichromatic_components,
    switched_coloring,
)


SCHEMA = "fourcolor-v24-factor-interface-audit-v1"
COLOR_MASK = 0b111


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_factor_interface_audit.json"),
    )
    return parser.parse_args()


def enumerate_colorings(
    edges: list[tuple[int, int]], incident_edges: list[list[int]]
) -> list[bytes]:
    colors = [-1] * len(edges)
    used_masks = [0] * len(incident_edges)
    solutions: list[bytes] = []

    def domain_mask(edge_index: int) -> int:
        left, right = edges[edge_index]
        return COLOR_MASK & ~(used_masks[left] | used_masks[right])

    def search() -> None:
        best_edge: int | None = None
        best_mask = 0
        best_size = 4
        for edge_index, color in enumerate(colors):
            if color != -1:
                continue
            mask = domain_mask(edge_index)
            size = mask.bit_count()
            if size == 0:
                return
            if size < best_size:
                best_edge, best_mask, best_size = edge_index, mask, size
        if best_edge is None:
            solutions.append(bytes(colors))
            return

        left, right = edges[best_edge]
        for color in range(3):
            if not (best_mask & (1 << color)):
                continue
            colors[best_edge] = color
            used_masks[left] |= 1 << color
            used_masks[right] |= 1 << color
            search()
            used_masks[left] ^= 1 << color
            used_masks[right] ^= 1 << color
            colors[best_edge] = -1

    search()
    return solutions


def missing_color(
    coloring: bytes, vertex: int, incident_edges: list[list[int]]
) -> int:
    missing = {0, 1, 2} - {coloring[edge] for edge in incident_edges[vertex]}
    if len(missing) != 1:
        raise AssertionError("a defect does not request a unique missing colour")
    return missing.pop()


def class_audit(
    solutions: list[bytes],
    accepting: set[int],
    edges: list[tuple[int, int]],
    incident_edges: list[list[int]],
    frozen_edges: set[int],
) -> dict[str, Any]:
    solution_index = {solution: index for index, solution in enumerate(solutions)}
    adjacency = [set() for _ in solutions]
    transition_edges: set[tuple[int, int]] = set()

    for source, coloring in enumerate(solutions):
        for pair in COLOR_PAIRS:
            for component in bichromatic_components(
                coloring, pair, edges, incident_edges
            ):
                if not component.isdisjoint(frozen_edges):
                    continue
                target_coloring = switched_coloring(coloring, pair, component)
                target = solution_index.get(target_coloring)
                if target is None:
                    raise AssertionError("a legal switch left the coloring census")
                adjacency[source].add(target)
                adjacency[target].add(source)
                transition_edges.add(tuple(sorted((source, target))))

    seen: set[int] = set()
    class_sizes: list[int] = []
    bad_classes: list[list[int]] = []
    for start in range(len(solutions)):
        if start in seen:
            continue
        queue = deque([start])
        seen.add(start)
        members: list[int] = []
        has_accepting = False
        while queue:
            source = queue.popleft()
            members.append(source)
            has_accepting = has_accepting or source in accepting
            for target in adjacency[source]:
                if target not in seen:
                    seen.add(target)
                    queue.append(target)
        class_sizes.append(len(members))
        if not has_accepting:
            bad_classes.append(members)

    witness = None
    if bad_classes:
        witness_index = min(bad_classes[0])
        witness = {
            "class_size": len(bad_classes[0]),
            "coloring_index": witness_index,
            "coloring": list(solutions[witness_index]),
        }
    return {
        "frozen_edge_count": len(frozen_edges),
        "transition_edge_count": len(transition_edges),
        "kempe_class_count": len(class_sizes),
        "accepting_class_count": len(class_sizes) - len(bad_classes),
        "noncompletable_class_count": len(bad_classes),
        "largest_class_size": max(class_sizes, default=0),
        "largest_noncompletable_class_size": max(
            (len(members) for members in bad_classes), default=0
        ),
        "witness": witness,
    }


def run() -> dict[str, Any]:
    instance = make_instance("C30")
    original_edges = [tuple(edge) for edge in instance["tangle_edges"]]
    original_incidence = instance["incident_edges"]
    outer = set(instance["outer_spokes"])
    inner = set(instance["inner_spokes"])
    boundary = outer | inner

    deleted_edge_index = next(
        edge_index
        for edge_index, edge in enumerate(original_edges)
        if edge_index not in boundary
        and all(len(original_incidence[vertex]) == 3 for vertex in edge)
    )
    defects = original_edges[deleted_edge_index]
    retained_indices = [
        edge_index
        for edge_index in range(len(original_edges))
        if edge_index != deleted_edge_index
    ]
    old_to_new = {
        old_index: new_index
        for new_index, old_index in enumerate(retained_indices)
    }
    edges = [original_edges[index] for index in retained_indices]
    incident_edges = [[] for _ in original_incidence]
    for edge_index, (left, right) in enumerate(edges):
        incident_edges[left].append(edge_index)
        incident_edges[right].append(edge_index)

    solutions = enumerate_colorings(edges, incident_edges)
    accepting = {
        index
        for index, coloring in enumerate(solutions)
        if missing_color(coloring, defects[0], incident_edges)
        == missing_color(coloring, defects[1], incident_edges)
    }
    if len(accepting) != 5412:
        raise AssertionError(
            "restoring the deleted edge did not reproduce the C30 census"
        )

    frozen_sets = {
        "none": set(),
        "outer_only": {old_to_new[index] for index in outer},
        "inner_only": {old_to_new[index] for index in inner},
        "both": {old_to_new[index] for index in boundary},
    }
    rows = {
        name: class_audit(
            solutions, accepting, edges, incident_edges, frozen_edges
        )
        for name, frozen_edges in frozen_sets.items()
    }
    if rows["none"]["noncompletable_class_count"] != 0:
        raise AssertionError("the unrestricted audit must be completable")
    if rows["outer_only"]["noncompletable_class_count"] != 0:
        raise AssertionError("the outer-only regression unexpectedly failed")
    if rows["inner_only"]["noncompletable_class_count"] != 0:
        raise AssertionError("the inner-only regression unexpectedly failed")
    if rows["both"]["noncompletable_class_count"] == 0:
        raise AssertionError("the twice-frozen regression failed to find its witness")

    digest = hashlib.sha256(b"".join(solutions)).hexdigest()
    return {
        "schema": SCHEMA,
        "purpose": "regression against naive all-seams-frozen factor independence",
        "source_instance": "C30 polar annulus",
        "source_graph_hash": instance["graph_hash"],
        "deleted_edge_index": deleted_edge_index,
        "deleted_edge": list(original_edges[deleted_edge_index]),
        "defect_vertices": list(defects),
        "retained_edge_count": len(edges),
        "coloring_count": len(solutions),
        "accepting_coloring_count": len(accepting),
        "coloring_fingerprint": digest,
        "audits": rows,
        "scope_warning": (
            "This refutes only the generic twice-frozen strengthening; it is "
            "not asserted to be a Kauffman factor or a Trail-Completability "
            "counterexample."
        ),
    }


def main() -> int:
    args = parse_args()
    result = run()
    atomic_write_json(args.output, result)
    print(
        f"colorings={result['coloring_count']} "
        f"accepting={result['accepting_coloring_count']}"
    )
    for name, row in result["audits"].items():
        print(
            f"{name}: classes={row['kempe_class_count']} "
            f"noncompletable={row['noncompletable_class_count']}"
        )
    print(f"certificate={args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
