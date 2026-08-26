#!/usr/bin/env python3
"""Exhaust a planar counterexample to generic square transport for WC*.

The specimen starts from the planar Frucht graph.  It replaces the disjoint
cofacial edges ``06`` and ``34`` by a facial square and opens the two
cofacial exterior edges ``5,10`` and ``8,11`` into four stubs.  The target
word has the colour-invariant form ``(a,a,b,b)`` with ``a != b``: the two
stubs cut from either edge agree, while the two restored edge colours differ.

Both planar square reductions satisfy WC* for this target.  The first does
so vacuously because it has no target colouring; the second has target
colourings and one Kempe class.  Upstairs the target is nonempty but lies in
only one of two Kempe classes, so WC* fails.

This refutes square transport for an arbitrary target, even when the target
is invariant under all colour permutations.  It does not refute the
route-specific theorem, whose target is the pentagonal extendable-word set
in a least obstruction.  All searches below are finite
and exhaustive; the hard-coded rotations also audit spherical planarity,
one-face placement of all four stubs, and the absence of internal bridges.
"""

from __future__ import annotations

from collections import defaultdict
import json

from v24_a_nonempty_counterexample import face_orbits, tait_colourings
from v24_sq3_migration_counterexample import (
    has_internal_bridge,
    kempe_classes,
)


EXTERIOR_EDGES = (
    (0, 1), (0, 7),
    (1, 2), (1, 7),
    (2, 3), (2, 8),
    (3, 9),
    (4, 5), (4, 9),
    (5, 6),
    (6, 10),
    (7, 11),
    (8, 9),
    (10, 11),
    (5, 16), (10, 17),
    (8, 18), (11, 19),
)
ATTACHMENTS = ((12, 0), (13, 6), (14, 4), (15, 3))
SQUARE_EDGES = ((12, 13), (13, 14), (14, 15), (15, 12))
EXPANDED_EDGES = EXTERIOR_EDGES + ATTACHMENTS + SQUARE_EDGES
REDUCTION_0_EDGES = EXTERIOR_EDGES + ((0, 6), (4, 3))
REDUCTION_1_EDGES = EXTERIOR_EDGES + ((6, 4), (3, 0))

EXPANDED_ROTATION = {
    0: (1, 7, 12), 1: (0, 2, 7), 2: (1, 3, 8),
    3: (2, 15, 9), 4: (5, 9, 14), 5: (16, 4, 6),
    6: (13, 10, 5), 7: (11, 0, 1), 8: (9, 18, 2),
    9: (3, 4, 8), 10: (11, 17, 6), 11: (19, 10, 7),
    12: (13, 15, 0), 13: (14, 12, 6),
    14: (4, 15, 13), 15: (12, 14, 3),
    16: (5,), 17: (10,), 18: (8,), 19: (11,),
}
REDUCTION_0_ROTATION = {
    0: (1, 7, 6), 1: (0, 2, 7), 2: (1, 3, 8),
    3: (2, 4, 9), 4: (5, 9, 3), 5: (16, 4, 6),
    6: (5, 0, 10), 7: (11, 0, 1), 8: (9, 18, 2),
    9: (3, 4, 8), 10: (11, 17, 6), 11: (19, 10, 7),
    16: (5,), 17: (10,), 18: (8,), 19: (11,),
}
REDUCTION_1_ROTATION = {
    0: (1, 7, 3), 1: (0, 2, 7), 2: (1, 3, 8),
    3: (2, 0, 9), 4: (5, 9, 6), 5: (16, 4, 6),
    6: (4, 10, 5), 7: (11, 0, 1), 8: (9, 18, 2),
    9: (3, 4, 8), 10: (11, 17, 6), 11: (19, 10, 7),
    16: (5,), 17: (10,), 18: (8,), 19: (11,),
}

STUB_EDGES = ((5, 16), (10, 17), (8, 18), (11, 19))
STUB_VERTICES = {16, 17, 18, 19}


def audit_map(
    edges: tuple[tuple[int, int], ...],
    rotation: dict[int, tuple[int, ...]],
    internal: tuple[int, ...],
) -> tuple[list[tuple[int, ...]], list[list[int]], list[list[int]]]:
    """Audit the map and compute its exact Tait/Kempe state space."""
    faces = face_orbits(edges, rotation)
    colourings, incident = tait_colourings(edges, internal)
    classes = kempe_classes(edges, colourings, incident)
    assert len(rotation) - len(edges) + len(faces) == 2
    assert any(STUB_VERTICES <= set(face) for face in faces)
    assert not has_internal_bridge(edges, internal)
    return colourings, classes, faces


def target_indices(edges: tuple[tuple[int, int], ...]) -> tuple[int, ...]:
    return tuple(edges.index(edge) for edge in STUB_EDGES)


def is_target(colouring: tuple[int, ...], indices: tuple[int, ...]) -> bool:
    first_left, first_right, second_left, second_right = indices
    return (
        colouring[first_left] == colouring[first_right]
        and colouring[second_left] == colouring[second_right]
        and colouring[first_left] != colouring[second_left]
    )


def class_target_counts(
    colourings: list[tuple[int, ...]],
    classes: list[list[int]],
    indices: tuple[int, ...],
) -> list[int]:
    return [
        sum(is_target(colourings[state], indices) for state in component)
        for component in classes
    ]


def wcstar_holds(target_counts: list[int]) -> bool:
    """The source convention: the assertion is vacuous if W is empty."""
    return sum(target_counts) == 0 or all(count > 0 for count in target_counts)


def main() -> None:
    expanded, expanded_classes, expanded_faces = audit_map(
        EXPANDED_EDGES, EXPANDED_ROTATION, tuple(range(16))
    )
    first, first_classes, first_faces = audit_map(
        REDUCTION_0_EDGES, REDUCTION_0_ROTATION, tuple(range(12))
    )
    second, second_classes, second_faces = audit_map(
        REDUCTION_1_EDGES, REDUCTION_1_ROTATION, tuple(range(12))
    )

    expanded_targets = class_target_counts(
        expanded, expanded_classes, target_indices(EXPANDED_EDGES)
    )
    first_targets = class_target_counts(
        first, first_classes, target_indices(REDUCTION_0_EDGES)
    )
    second_targets = class_target_counts(
        second, second_classes, target_indices(REDUCTION_1_EDGES)
    )

    assert len(expanded) == 48
    assert list(map(len, expanded_classes)) == [18, 30]
    assert expanded_targets in ([0, 6], [6, 0])
    assert not wcstar_holds(expanded_targets)
    assert [12, 13, 14, 15] in expanded_faces

    assert len(first) == 30
    assert list(map(len, first_classes)) == [30]
    assert wcstar_holds(first_targets)

    assert len(second) == 18
    assert list(map(len, second_classes)) == [18]
    assert wcstar_holds(second_targets)

    print(
        json.dumps(
            {
                "target": {
                    "description": "(a,a,b,b) with a != b",
                    "opened_edges": [[5, 10], [8, 11]],
                },
                "expanded": {
                    "vertices": len(EXPANDED_ROTATION),
                    "edges": len(EXPANDED_EDGES),
                    "faces": len(expanded_faces),
                    "tait_colourings": len(expanded),
                    "kempe_class_sizes": list(map(len, expanded_classes)),
                    "target_counts_by_class": expanded_targets,
                    "wcstar": wcstar_holds(expanded_targets),
                },
                "reduction_0": {
                    "faces": len(first_faces),
                    "tait_colourings": len(first),
                    "kempe_class_sizes": list(map(len, first_classes)),
                    "target_counts_by_class": first_targets,
                    "wcstar": wcstar_holds(first_targets),
                },
                "reduction_1": {
                    "faces": len(second_faces),
                    "tait_colourings": len(second),
                    "kempe_class_sizes": list(map(len, second_classes)),
                    "target_counts_by_class": second_targets,
                    "wcstar": wcstar_holds(second_targets),
                },
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
