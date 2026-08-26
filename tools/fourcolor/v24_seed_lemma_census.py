#!/usr/bin/env python3
"""Exhaust the cap-correct Seed predicate on the C24/C30/C40 laboratories.

For every pair of vertex-disjoint pentagonal faces, remove both cap cycles,
enumerate every Tait colouring of the resulting five-by-five boundary
instance, group states by the ordered inner word, and test the actual Menu-B
criterion after restoring the inner cap.  Connectivity is recorded but is
not imposed: the literal source and Lean boundary data do not require it,
and some published C24 instances have an isolated edge between the two cap
boundaries.

  some majority colour pair has at least two distinct Kempe components
  meeting the cap.

This deliberately does not count components in the open tangle, where the
degree-one spokes make the lower bound vacuous.  The run is exhaustive and
deterministic.  It is a finite audit of three graph families, not a proof of
the universal Seed Lemma.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from itertools import combinations, product
import json


def dual_c24() -> tuple[list[frozenset[int]], int]:
    ring = lambda i: 2 + (i % 12)
    triangles: list[frozenset[int]] = []
    for i in range(0, 12, 2):
        triangles.append(frozenset((0, ring(i), ring(i + 2))))
        triangles.append(frozenset((1, ring(i + 1), ring(i + 3))))
    for i in range(12):
        triangles.append(frozenset((ring(i), ring(i + 1), ring(i + 2))))
    return triangles, 14


def dual_tube(levels: int) -> tuple[list[frozenset[int]], int]:
    ids: dict[object, int] = {}

    def vertex(name: object) -> int:
        if name not in ids:
            ids[name] = len(ids)
        return ids[name]

    north, south = vertex("N"), vertex("S")
    top = [vertex(("A", i)) for i in range(5)]
    middle = [
        [vertex(("H", level, i)) for i in range(5)]
        for level in range(levels)
    ]
    bottom = [vertex(("B", i)) for i in range(5)]
    triangles: list[frozenset[int]] = []
    for i in range(5):
        triangles.append(frozenset((north, top[i], top[(i + 1) % 5])))
        triangles.append(frozenset((south, bottom[i], bottom[(i + 1) % 5])))
    rings = [top] + middle + [bottom]
    for upper, lower in zip(rings, rings[1:]):
        for i in range(5):
            triangles.append(
                frozenset((upper[i], lower[i], lower[(i + 1) % 5]))
            )
            triangles.append(
                frozenset((upper[i], upper[(i + 1) % 5], lower[(i + 1) % 5]))
            )
    return triangles, len(ids)


def build_fullerene(
    triangles: list[frozenset[int]], point_count: int
) -> tuple[list[set[int]], list[tuple[int, int]], list[tuple[int, list[int]]], list[int]]:
    edge_triangles: dict[tuple[int, int], list[int]] = defaultdict(list)
    for triangle_index, triangle in enumerate(triangles):
        for edge in combinations(sorted(triangle), 2):
            edge_triangles[edge].append(triangle_index)

    neighbours = [set() for _ in triangles]
    edges: list[tuple[int, int]] = []
    for incident in edge_triangles.values():
        assert len(incident) == 2
        left, right = incident
        neighbours[left].add(right)
        neighbours[right].add(left)
        edges.append(tuple(sorted((left, right))))
    edges = sorted(set(edges))
    assert all(len(adjacency) == 3 for adjacency in neighbours)

    point_triangles: dict[int, list[int]] = defaultdict(list)
    for triangle_index, triangle in enumerate(triangles):
        for point in triangle:
            point_triangles[point].append(triangle_index)

    faces: list[tuple[int, list[int]]] = []
    for point in range(point_count):
        around = set(point_triangles[point])
        start = min(around)
        cycle = [start]
        previous: int | None = None
        current = start
        while True:
            choices = [
                neighbour
                for neighbour in neighbours[current]
                if neighbour in around and neighbour != previous
            ]
            assert 1 <= len(choices) <= 2
            following = choices[0]
            if following == start:
                break
            cycle.append(following)
            previous, current = current, following
        assert len(cycle) == len(around)
        faces.append((point, cycle))

    pentagons = [
        face_index for face_index, (_, cycle) in enumerate(faces)
        if len(cycle) == 5
    ]
    assert len(pentagons) == 12
    return neighbours, edges, faces, pentagons


def build_family(
    name: str,
) -> tuple[list[set[int]], list[tuple[int, int]], list[tuple[int, list[int]]], list[int]]:
    if name == "C24":
        triangles, point_count = dual_c24()
    elif name == "C30":
        triangles, point_count = dual_tube(1)
    elif name == "C40":
        triangles, point_count = dual_tube(2)
    else:
        raise ValueError(name)
    triangles = sorted(triangles, key=sorted)
    return build_fullerene(triangles, point_count)


def two_hole_tangle(
    neighbours: list[set[int]],
    edges: list[tuple[int, int]],
    faces: list[tuple[int, list[int]]],
    outer_face: int,
    inner_face: int,
) -> tuple[
    list[tuple[int, int]], list[list[int]], dict[str, list[int]],
    dict[str, list[int]], bool
]:
    caps = {
        "outer": faces[outer_face][1],
        "inner": faces[inner_face][1],
    }
    assert not (set(caps["outer"]) & set(caps["inner"]))
    deleted: set[tuple[int, int]] = set()
    for cap in caps.values():
        for left, right in zip(cap, cap[1:] + cap[:1]):
            deleted.add(tuple(sorted((left, right))))
    tangle_edges = [edge for edge in edges if edge not in deleted]
    incidence = [[] for _ in neighbours]
    for edge_index, (left, right) in enumerate(tangle_edges):
        incidence[left].append(edge_index)
        incidence[right].append(edge_index)
    spokes: dict[str, list[int]] = {}
    for tag, cap in caps.items():
        cap_set = set(cap)
        spoke_indices: list[int] = []
        for vertex in cap:
            outside = [u for u in neighbours[vertex] if u not in cap_set]
            assert len(outside) == 1
            spoke_indices.append(
                tangle_edges.index(tuple(sorted((vertex, outside[0]))))
            )
        spokes[tag] = spoke_indices

    cap_vertices = set(caps["outer"]) | set(caps["inner"])
    assert all(
        len(incidence[vertex]) == (1 if vertex in cap_vertices else 3)
        for vertex in range(len(neighbours))
    )
    reached = {0}
    stack = [0]
    while stack:
        vertex = stack.pop()
        for edge_index in incidence[vertex]:
            left, right = tangle_edges[edge_index]
            other = right if vertex == left else left
            if other not in reached:
                reached.add(other)
                stack.append(other)
    connected = len(reached) == len(neighbours)
    return tangle_edges, incidence, spokes, caps, connected


def enumerate_colourings(
    edges: list[tuple[int, int]], incidence: list[list[int]]
) -> list[tuple[int, ...]]:
    colours = [-1] * len(edges)
    solutions: list[tuple[int, ...]] = []

    def legal(edge_index: int, colour: int) -> bool:
        return all(
            all(
                other == edge_index or colours[other] != colour
                for other in incidence[vertex]
            )
            for vertex in edges[edge_index]
        )

    def search(position: int) -> None:
        if position == len(edges):
            solutions.append(tuple(colours))
            return
        for colour in range(3):
            if legal(position, colour):
                colours[position] = colour
                search(position + 1)
                colours[position] = -1

    search(0)
    return solutions


def good_word(word: tuple[int, ...]) -> bool:
    counts = Counter(word)
    if sorted(counts.values()) != [1, 1, 3]:
        return False
    majority = next(colour for colour, count in counts.items() if count == 3)
    return any(
        all(word[(start + offset) % 5] == majority for offset in range(3))
        for start in range(5)
    )


CAP_EXTENSION: dict[tuple[int, ...], tuple[int, ...]] = {}
for word in product(range(3), repeat=5):
    if not good_word(word):
        continue
    extensions = [
        internal
        for internal in product(range(3), repeat=5)
        if all(
            {word[index], internal[index - 1], internal[index]} == {0, 1, 2}
            for index in range(5)
        )
    ]
    assert len(extensions) == 1
    CAP_EXTENSION[word] = extensions[0]


def menu_b(
    colouring: tuple[int, ...],
    tangle_edges: list[tuple[int, int]],
    incidence: list[list[int]],
    inner_spokes: list[int],
    inner_cap: list[int],
) -> bool:
    word = tuple(colouring[edge] for edge in inner_spokes)
    internal_colours = CAP_EXTENSION[word]
    edges = list(tangle_edges)
    colours = list(colouring)
    full_incidence = [list(row) for row in incidence]
    for index, colour in enumerate(internal_colours):
        left, right = inner_cap[index], inner_cap[(index + 1) % 5]
        edge_index = len(edges)
        edges.append((left, right))
        colours.append(colour)
        full_incidence[left].append(edge_index)
        full_incidence[right].append(edge_index)

    majority = Counter(word).most_common(1)[0][0]
    for other in range(3):
        if other == majority:
            continue
        allowed = {majority, other}
        unseen = {
            edge_index
            for edge_index, colour in enumerate(colours)
            if colour in allowed
        }
        component_of: dict[int, int] = {}
        component_index = 0
        while unseen:
            seed = unseen.pop()
            component = {seed}
            stack = [seed]
            while stack:
                edge_index = stack.pop()
                for vertex in edges[edge_index]:
                    for adjacent in full_incidence[vertex]:
                        if adjacent in unseen:
                            unseen.remove(adjacent)
                            component.add(adjacent)
                            stack.append(adjacent)
            for edge_index in component:
                component_of[edge_index] = component_index
            component_index += 1
        active_spokes = [
            edge for edge in inner_spokes if colours[edge] in allowed
        ]
        if len({component_of[edge] for edge in active_spokes}) >= 2:
            return True
    return False


def audit_family(name: str) -> dict:
    neighbours, edges, faces, pentagons = build_family(name)
    spectra: Counter[tuple[int, int, int, int]] = Counter()
    candidate_pairs = disconnected_pairs = 0
    annuli = good_fibres = good_states = menu_b_states = seedless = 0
    for outer_index, inner_index in combinations(pentagons, 2):
        if set(faces[outer_index][1]) & set(faces[inner_index][1]):
            continue
        candidate_pairs += 1
        tangle_edges, incidence, spokes, caps, connected = two_hole_tangle(
            neighbours, edges, faces, outer_index, inner_index
        )
        if not connected:
            disconnected_pairs += 1
        colourings = enumerate_colourings(tangle_edges, incidence)
        fibres: dict[tuple[int, ...], list[tuple[int, ...]]] = defaultdict(list)
        for colouring in colourings:
            word = tuple(colouring[edge] for edge in spokes["inner"])
            if good_word(word):
                fibres[word].append(colouring)
        local_menu_b = 0
        local_seedless = 0
        for fibre in fibres.values():
            flags = [
                menu_b(
                    colouring,
                    tangle_edges,
                    incidence,
                    spokes["inner"],
                    caps["inner"],
                )
                for colouring in fibre
            ]
            local_menu_b += sum(flags)
            local_seedless += not any(flags)
        local_good_states = sum(map(len, fibres.values()))
        spectra[
            (len(colourings), local_good_states, local_menu_b, local_seedless)
        ] += 1
        annuli += 1
        good_fibres += len(fibres)
        good_states += local_good_states
        menu_b_states += local_menu_b
        seedless += local_seedless
    return {
        "candidate_pairs": candidate_pairs,
        "disconnected_pairs": disconnected_pairs,
        "annuli": annuli,
        "good_fibres": good_fibres,
        "good_states": good_states,
        "menu_b_states": menu_b_states,
        "seedless_fibres": seedless,
        "spectra": [
            {
                "colourings": key[0],
                "good_states": key[1],
                "menu_b_states": key[2],
                "seedless_fibres": key[3],
                "annuli": count,
            }
            for key, count in sorted(spectra.items())
        ],
    }


EXPECTED = {
    "C24": (42, 24, 42, 1260, 10080, 9036, 0),
    "C30": (46, 15, 46, 1380, 23400, 17340, 0),
    "C40": (46, 10, 46, 1380, 118320, 89580, 0),
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "families", nargs="*", choices=sorted(EXPECTED)
    )
    args = parser.parse_args()
    families = args.families or sorted(EXPECTED)
    results = {name: audit_family(name) for name in families}
    for name, result in results.items():
        observed = (
            result["candidate_pairs"],
            result["disconnected_pairs"],
            result["annuli"],
            result["good_fibres"],
            result["good_states"],
            result["menu_b_states"],
            result["seedless_fibres"],
        )
        assert observed == EXPECTED[name], (name, observed, EXPECTED[name])
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
