#!/usr/bin/env python3
"""Exhaust a planar tangle counterexample to universal SQ3 migration.

Start from the planar Frucht graph, select the disjoint cofacial edges
``06`` and ``34``, replace them by a facial square, and open the unrelated
edge ``01`` into two stubs.  Both planar square reductions have connected
Kempe reconfiguration graphs.  The expanded tangle does not: its 18 Tait
colourings split into classes of sizes 6 and 12, exactly the two reduction
sides, and the all-equal overlap is empty.

This refutes the universal implication

    connected(G0) and connected(G1)  ==>  connected(G),

not the weaker target-specific WC* statement used by the route.  The two
stubs lie on one face in every hard-coded spherical rotation below.
"""

from __future__ import annotations

from collections import defaultdict
import json

from v24_a_nonempty_counterexample import face_orbits, tait_colourings


EXTERIOR_EDGES = (
    (0, 7),
    (1, 2), (1, 7),
    (2, 3), (2, 8),
    (3, 9),
    (4, 5), (4, 9),
    (5, 6), (5, 10),
    (6, 10),
    (7, 11),
    (8, 11), (8, 9),
    (10, 11),
    (0, 16), (1, 17),
)
ATTACHMENTS = ((12, 0), (13, 6), (14, 4), (15, 3))
SQUARE_EDGES = ((12, 13), (13, 14), (14, 15), (15, 12))
EXPANDED_EDGES = EXTERIOR_EDGES + ATTACHMENTS + SQUARE_EDGES
REDUCTION_0_EDGES = EXTERIOR_EDGES + ((0, 6), (4, 3))
REDUCTION_1_EDGES = EXTERIOR_EDGES + ((6, 4), (3, 0))

EXPANDED_ROTATION = {
    0: (16, 7, 12), 1: (17, 2, 7), 2: (1, 3, 8),
    3: (2, 15, 9), 4: (5, 9, 14), 5: (10, 4, 6),
    6: (13, 10, 5), 7: (11, 0, 1), 8: (9, 11, 2),
    9: (3, 4, 8), 10: (11, 5, 6), 11: (8, 10, 7),
    12: (13, 15, 0), 13: (14, 12, 6),
    14: (4, 15, 13), 15: (12, 14, 3),
    16: (0,), 17: (1,),
}
REDUCTION_0_ROTATION = {
    0: (16, 7, 6), 1: (17, 2, 7), 2: (1, 3, 8),
    3: (2, 4, 9), 4: (5, 9, 3), 5: (10, 4, 6),
    6: (5, 0, 10), 7: (11, 0, 1), 8: (9, 11, 2),
    9: (3, 4, 8), 10: (11, 5, 6), 11: (8, 10, 7),
    16: (0,), 17: (1,),
}
REDUCTION_1_ROTATION = {
    0: (16, 7, 3), 1: (17, 2, 7), 2: (1, 3, 8),
    3: (2, 0, 9), 4: (5, 9, 6), 5: (10, 4, 6),
    6: (4, 10, 5), 7: (11, 0, 1), 8: (9, 11, 2),
    9: (3, 4, 8), 10: (11, 5, 6), 11: (8, 10, 7),
    16: (0,), 17: (1,),
}


def kempe_classes(
    edges: tuple[tuple[int, int], ...],
    colourings: list[tuple[int, ...]],
    incident: dict[int, list[int]],
) -> list[list[int]]:
    """Compute connected components of the exact Kempe-switch graph."""
    index = {colouring: i for i, colouring in enumerate(colourings)}
    adjacency = [set() for _ in colourings]
    for source, colouring in enumerate(colourings):
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
                target = index[tuple(switched)]
                adjacency[source].add(target)
                adjacency[target].add(source)

    seen: set[int] = set()
    classes: list[list[int]] = []
    for start in range(len(colourings)):
        if start in seen:
            continue
        seen.add(start)
        stack = [start]
        component: list[int] = []
        while stack:
            state = stack.pop()
            component.append(state)
            for target in adjacency[state]:
                if target not in seen:
                    seen.add(target)
                    stack.append(target)
        classes.append(sorted(component))
    return sorted(classes, key=len)


def has_internal_bridge(
    edges: tuple[tuple[int, int], ...], internal: tuple[int, ...]
) -> bool:
    """Test bridges by deleting each indexed internal edge in turn."""
    internal_set = set(internal)
    vertices = {v for edge in edges for v in edge}
    for removed, (left, right) in enumerate(edges):
        if left not in internal_set or right not in internal_set:
            continue
        adjacency: dict[int, list[int]] = defaultdict(list)
        for index, (u, v) in enumerate(edges):
            if index == removed:
                continue
            adjacency[u].append(v)
            adjacency[v].append(u)
        reached = {left}
        stack = [left]
        while stack:
            u = stack.pop()
            for v in adjacency[u]:
                if v not in reached:
                    reached.add(v)
                    stack.append(v)
        if right not in reached or reached != vertices:
            return True
    return False


def audit_map(
    edges: tuple[tuple[int, int], ...],
    rotation: dict[int, tuple[int, ...]],
    internal: tuple[int, ...],
) -> tuple[list[tuple[int, ...]], list[list[int]], list[list[int]]]:
    faces = face_orbits(edges, rotation)
    colourings, incident = tait_colourings(edges, internal)
    classes = kempe_classes(edges, colourings, incident)
    assert len(rotation) - len(edges) + len(faces) == 2
    assert any(16 in face and 17 in face for face in faces)
    assert not has_internal_bridge(edges, internal)
    return colourings, classes, faces


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

    attachment_indices = [EXPANDED_EDGES.index(edge) for edge in ATTACHMENTS]
    expanded_stub_indices = [
        EXPANDED_EDGES.index((0, 16)), EXPANDED_EDGES.index((1, 17))
    ]
    first_stub_indices = [
        REDUCTION_0_EDGES.index((0, 16)), REDUCTION_0_EDGES.index((1, 17))
    ]
    second_stub_indices = [
        REDUCTION_1_EDGES.index((0, 16)), REDUCTION_1_EDGES.index((1, 17))
    ]

    def side(word: tuple[int, ...]) -> int:
        side_0 = word[0] == word[1] and word[2] == word[3]
        side_1 = word[1] == word[2] and word[3] == word[0]
        assert side_0 != side_1  # all-equal is absent in this specimen
        return 0 if side_0 else 1

    all_equal = 0
    class_side_counts = []
    for component in expanded_classes:
        counts = [0, 0]
        for state in component:
            word = tuple(expanded[state][i] for i in attachment_indices)
            all_equal += len(set(word)) == 1
            counts[side(word)] += 1
        class_side_counts.append(counts)

    assert len(first) == 6 and list(map(len, first_classes)) == [6]
    assert len(second) == 12 and list(map(len, second_classes)) == [12]
    assert len(expanded) == 18
    assert list(map(len, expanded_classes)) == [6, 12]
    assert class_side_counts == [[6, 0], [0, 12]]
    assert all_equal == 0
    assert [12, 13, 14, 15] in expanded_faces
    assert all(c[expanded_stub_indices[0]] == c[expanded_stub_indices[1]]
               for c in expanded)
    assert all(c[first_stub_indices[0]] == c[first_stub_indices[1]]
               for c in first)
    assert all(c[second_stub_indices[0]] == c[second_stub_indices[1]]
               for c in second)

    print(
        json.dumps(
            {
                "expanded": {
                    "vertices": len(EXPANDED_ROTATION),
                    "edges": len(EXPANDED_EDGES),
                    "faces": len(expanded_faces),
                    "tait_colourings": len(expanded),
                    "kempe_class_sizes": list(map(len, expanded_classes)),
                    "class_reduction_side_counts": class_side_counts,
                    "all_equal_square_boundary_colourings": all_equal,
                    "all_stub_words_extendable": True,
                },
                "reduction_0": {
                    "faces": len(first_faces),
                    "tait_colourings": len(first),
                    "kempe_class_sizes": list(map(len, first_classes)),
                },
                "reduction_1": {
                    "faces": len(second_faces),
                    "tait_colourings": len(second),
                    "kempe_class_sizes": list(map(len, second_classes)),
                },
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
