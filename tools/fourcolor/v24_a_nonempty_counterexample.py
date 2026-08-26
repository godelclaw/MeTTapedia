#!/usr/bin/env python3
"""Exhaust a planar counterexample to Addendum XXVI's ``A != empty``.

The reduced tangle is a triangular prism with one edge opened into two
stubs.  The marked edges are disjoint and cofacial, but receive different
colours in every Tait colouring.  Re-inserting the facial square shows that
this is not merely an arbitrary marked-edge example: the marked edges are
exactly one planar square reduction.

The audit also records what the counterexample does *not* refute.  The
expanded square tangle has one Kempe class even though its all-equal square
fibre is empty.  Its first reduction has six colourings and its other
(parallel-edge) reduction has none, so the additive square identity reads
``6 = 6 + 0``.  Thus the universal nonemptiness shortcut is false while this
specimen still satisfies the square conclusion by a different route.

Edges are indexed, rather than represented as a simple graph, because the
second planar reduction contains parallel edges.  The search is exhaustive
and small; no randomized or heuristic step is used.
"""

from __future__ import annotations

from collections import defaultdict
import json


REDUCED_EDGES = (
    (0, 1), (0, 2), (0, 3), (1, 4), (1, 5),
    (2, 3), (2, 5), (3, 4), (4, 6), (5, 7),
)
REDUCED_ROTATION = {
    0: (1, 2, 3), 1: (0, 4, 5), 2: (3, 0, 5), 3: (4, 0, 2),
    4: (1, 3, 6), 5: (2, 1, 7), 6: (4,), 7: (5,),
}
REDUCED_INTERNAL = tuple(range(6))
STUBS = (6, 7)
SELECTED = ((0, 1), (3, 4))

# Delete the marked edges, insert a square 8--9--10--11--8, and attach its
# vertices in the cyclic order 0,1,4,3.  Suppressing the square along the
# 01|23 pairing restores SELECTED.  The other pairing duplicates (1,4) and
# (0,3), so it must be treated as a multigraph.
EXTERIOR_EDGES = (
    (0, 2), (0, 3), (1, 4), (1, 5),
    (2, 3), (2, 5), (4, 6), (5, 7),
)
ATTACHMENTS = ((8, 0), (9, 1), (10, 4), (11, 3))
SQUARE_EDGES = ((8, 9), (9, 10), (10, 11), (11, 8))
EXPANDED_EDGES = EXTERIOR_EDGES + ATTACHMENTS + SQUARE_EDGES
EXPANDED_ROTATION = {
    0: (2, 8, 3), 1: (9, 5, 4), 2: (0, 3, 5), 3: (2, 0, 11),
    4: (1, 10, 6), 5: (1, 2, 7), 6: (4,), 7: (5,),
    8: (11, 0, 9), 9: (8, 1, 10), 10: (4, 11, 9), 11: (3, 8, 10),
}
EXPANDED_INTERNAL = tuple(range(6)) + (8, 9, 10, 11)


def canon(edge: tuple[int, int]) -> tuple[int, int]:
    return tuple(sorted(edge))


def face_orbits(
    edges: tuple[tuple[int, int], ...], rotation: dict[int, tuple[int, ...]]
) -> list[list[int]]:
    """Trace faces using the predecessor of the incoming dart."""
    unseen = {(u, v) for edge in edges for u, v in (edge, edge[::-1])}
    faces: list[list[int]] = []
    while unseen:
        start = min(unseen)
        dart = start
        face: list[int] = []
        while True:
            u, v = dart
            unseen.remove(dart)
            face.append(u)
            around = rotation[v]
            pos = around.index(u)
            dart = (v, around[(pos - 1) % len(around)])
            if dart == start:
                break
        faces.append(face)
    return faces


def tait_colourings(
    edges: tuple[tuple[int, int], ...], internal: tuple[int, ...]
) -> tuple[list[tuple[int, ...]], dict[int, list[int]]]:
    """Enumerate proper three-edge-colourings by exact backtracking."""
    internal_set = set(internal)
    incident: dict[int, list[int]] = defaultdict(list)
    for index, (u, v) in enumerate(edges):
        incident[u].append(index)
        incident[v].append(index)
    order = sorted(
        range(len(edges)),
        key=lambda i: -sum(v in internal_set for v in edges[i]),
    )
    assignment = [-1] * len(edges)
    out: list[tuple[int, ...]] = []

    def locally_proper(vertex: int) -> bool:
        used = [assignment[i] for i in incident[vertex] if assignment[i] >= 0]
        return len(used) == len(set(used))

    def search(position: int) -> None:
        if position == len(order):
            out.append(tuple(assignment))
            return
        edge_index = order[position]
        u, v = edges[edge_index]
        for colour in range(3):
            assignment[edge_index] = colour
            if (
                (u not in internal_set or locally_proper(u))
                and (v not in internal_set or locally_proper(v))
            ):
                search(position + 1)
        assignment[edge_index] = -1

    search(0)
    return out, incident


def kempe_class_sizes(
    edges: tuple[tuple[int, int], ...],
    colourings: list[tuple[int, ...]],
    incident: dict[int, list[int]],
) -> list[int]:
    """Return components of the full legal Kempe-switch graph."""
    index = {colouring: i for i, colouring in enumerate(colourings)}
    adjacency = [set() for _ in colourings]
    for source_index, colouring in enumerate(colourings):
        for first, second in ((0, 1), (0, 2), (1, 2)):
            unseen = {
                i for i, colour in enumerate(colouring)
                if colour in (first, second)
            }
            while unseen:
                seed = unseen.pop()
                component = {seed}
                stack = [seed]
                while stack:
                    edge_index = stack.pop()
                    for vertex in edges[edge_index]:
                        for neighbour in incident[vertex]:
                            if neighbour in unseen:
                                unseen.remove(neighbour)
                                component.add(neighbour)
                                stack.append(neighbour)
                switched = list(colouring)
                for edge_index in component:
                    switched[edge_index] = (
                        second if colouring[edge_index] == first else first
                    )
                target_index = index[tuple(switched)]
                adjacency[source_index].add(target_index)
                adjacency[target_index].add(source_index)

    seen: set[int] = set()
    sizes: list[int] = []
    for start in range(len(colourings)):
        if start in seen:
            continue
        seen.add(start)
        stack = [start]
        size = 0
        while stack:
            state = stack.pop()
            size += 1
            for target in adjacency[state]:
                if target not in seen:
                    seen.add(target)
                    stack.append(target)
        sizes.append(size)
    return sorted(sizes)


def audit_reduced() -> dict:
    faces = face_orbits(REDUCED_EDGES, REDUCED_ROTATION)
    colourings, incident = tait_colourings(REDUCED_EDGES, REDUCED_INTERNAL)
    edge_index = {canon(edge): i for i, edge in enumerate(REDUCED_EDGES)}
    first, second = (edge_index[canon(edge)] for edge in SELECTED)
    selected_face = next(
        face
        for face in faces
        if set(map(canon, SELECTED))
        <= {
            canon((u, v))
            for u, v in zip(face, face[1:] + face[:1])
        }
    )
    outer_face = next(face for face in faces if set(STUBS) <= set(face))
    class_sizes = kempe_class_sizes(REDUCED_EDGES, colourings, incident)

    assert len(faces) == 4
    assert len(REDUCED_ROTATION) - len(REDUCED_EDGES) + len(faces) == 2
    assert set(SELECTED[0]).isdisjoint(SELECTED[1])
    assert len(colourings) == 6
    assert class_sizes == [6]
    assert all(c[first] != c[second] for c in colourings)
    return {
        "vertices": len(REDUCED_ROTATION),
        "edges": len(REDUCED_EDGES),
        "faces": faces,
        "selected_face": selected_face,
        "outer_stub_face": outer_face,
        "tait_colourings": len(colourings),
        "kempe_class_sizes": class_sizes,
        "selected_equal_colourings": 0,
    }


def audit_expanded() -> dict:
    faces = face_orbits(EXPANDED_EDGES, EXPANDED_ROTATION)
    colourings, incident = tait_colourings(EXPANDED_EDGES, EXPANDED_INTERNAL)
    class_sizes = kempe_class_sizes(EXPANDED_EDGES, colourings, incident)
    attachment_indices = [EXPANDED_EDGES.index(edge) for edge in ATTACHMENTS]
    all_equal = sum(
        len({colouring[i] for i in attachment_indices}) == 1
        for colouring in colourings
    )

    reduction_01 = EXTERIOR_EDGES + ((0, 1), (4, 3))
    reduction_12 = EXTERIOR_EDGES + ((1, 4), (3, 0))
    first_colourings, first_incident = tait_colourings(
        reduction_01, REDUCED_INTERNAL
    )
    second_colourings, second_incident = tait_colourings(
        reduction_12, REDUCED_INTERNAL
    )
    first_classes = kempe_class_sizes(
        reduction_01, first_colourings, first_incident
    )
    second_classes = kempe_class_sizes(
        reduction_12, second_colourings, second_incident
    )

    assert len(faces) == 6
    assert len(EXPANDED_ROTATION) - len(EXPANDED_EDGES) + len(faces) == 2
    assert [8, 9, 10, 11] in faces
    assert len(colourings) == 6
    assert class_sizes == [6]
    assert all_equal == 0
    assert len(first_colourings) == 6 and first_classes == [6]
    assert len(second_colourings) == 0 and second_classes == []
    assert len(colourings) == len(first_colourings) + len(second_colourings)
    return {
        "vertices": len(EXPANDED_ROTATION),
        "edges": len(EXPANDED_EDGES),
        "faces": faces,
        "tait_colourings": len(colourings),
        "kempe_class_sizes": class_sizes,
        "all_equal_square_boundary_colourings": all_equal,
        "reduction_01_tait_colourings": len(first_colourings),
        "reduction_01_kempe_class_sizes": first_classes,
        "reduction_12_tait_colourings": len(second_colourings),
        "reduction_12_kempe_class_sizes": second_classes,
        "additive_square_identity": (
            f"{len(colourings)} = "
            f"{len(first_colourings)} + {len(second_colourings)}"
        ),
    }


def main() -> None:
    print(
        json.dumps(
            {
                "reduced_forced_unequal_witness": audit_reduced(),
                "inverse_planar_square_expansion": audit_expanded(),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
