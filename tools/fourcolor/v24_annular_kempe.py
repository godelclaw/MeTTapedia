#!/usr/bin/env python3
"""Independent Kempe-orbit analysis for the v24 annular census tangles."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Any, Iterable

from v24_annular_census import CensusSearch, atomic_write_json, make_instance


SCHEMA = "fourcolor-v24-annular-kempe-census-v1"
COLOR_PAIRS = ((0, 1), (0, 2), (1, 2))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Reproduce the v24 C30/C40 annular Kempe-class claims."
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


class UnionFind:
    def __init__(self, size: int):
        self.parent = list(range(size))
        self.rank = [0] * size

    def find(self, value: int) -> int:
        root = value
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[value] != value:
            parent = self.parent[value]
            self.parent[value] = root
            value = parent
        return root

    def union(self, left: int, right: int) -> None:
        left_root = self.find(left)
        right_root = self.find(right)
        if left_root == right_root:
            return
        if self.rank[left_root] < self.rank[right_root]:
            left_root, right_root = right_root, left_root
        self.parent[right_root] = left_root
        if self.rank[left_root] == self.rank[right_root]:
            self.rank[left_root] += 1


def is_good_word(word: tuple[int, ...]) -> bool:
    counts = Counter(word)
    if sorted(counts.values()) != [1, 1, 3]:
        return False
    majority = max(counts, key=counts.get)
    positions = {index for index, color in enumerate(word) if color == majority}
    return any(
        {(start + offset) % 5 for offset in range(3)} == positions
        for start in range(5)
    )


def bichromatic_components(
    coloring: bytes,
    pair: tuple[int, int],
    edges: list[tuple[int, int]],
    incident_edges: list[list[int]],
) -> Iterable[frozenset[int]]:
    eligible = {index for index, color in enumerate(coloring) if color in pair}
    while eligible:
        first = min(eligible)
        component = {first}
        eligible.remove(first)
        queue = deque([first])
        while queue:
            edge_index = queue.popleft()
            for vertex in edges[edge_index]:
                for neighbor_edge in incident_edges[vertex]:
                    if neighbor_edge in eligible:
                        eligible.remove(neighbor_edge)
                        component.add(neighbor_edge)
                        queue.append(neighbor_edge)
        yield frozenset(component)


def switched_coloring(
    coloring: bytes, pair: tuple[int, int], component: frozenset[int]
) -> bytes:
    left, right = pair
    switched = bytearray(coloring)
    for edge_index in component:
        color = switched[edge_index]
        switched[edge_index] = right if color == left else left
    return bytes(switched)


def class_sizes(union_find: UnionFind, members: Iterable[int]) -> list[int]:
    counts = Counter(union_find.find(member) for member in members)
    return sorted(counts.values(), reverse=True)


def enumerate_solutions(instance: dict[str, Any]) -> list[bytes]:
    solutions: list[bytes] = []
    for root_color in range(3):
        search = CensusSearch(instance, root_color, collect_solutions=True)
        search.search()
        if search.solutions is None:
            raise AssertionError("solution collection was not enabled")
        solutions.extend(search.solutions)
    if len(solutions) != len(set(solutions)):
        raise AssertionError("root-color shards overlap")
    return solutions


def analyze_graph(name: str) -> dict[str, Any]:
    instance = make_instance(name)
    edges = [tuple(edge) for edge in instance["tangle_edges"]]
    incident_edges = instance["incident_edges"]
    inner_spokes = frozenset(instance["inner_spokes"])
    solutions = enumerate_solutions(instance)
    solution_index = {solution: index for index, solution in enumerate(solutions)}

    full_moves = UnionFind(len(solutions))
    inner_avoiding_moves = UnionFind(len(solutions))
    full_transition_edges: set[tuple[int, int]] = set()
    inner_avoiding_transition_edges: set[tuple[int, int]] = set()

    for solution_number, coloring in enumerate(solutions):
        for pair in COLOR_PAIRS:
            for component in bichromatic_components(
                coloring, pair, edges, incident_edges
            ):
                switched = switched_coloring(coloring, pair, component)
                target = solution_index.get(switched)
                if target is None:
                    raise AssertionError("a Kempe switch left the coloring census")
                transition = tuple(sorted((solution_number, target)))
                full_transition_edges.add(transition)
                full_moves.union(solution_number, target)
                if component.isdisjoint(inner_spokes):
                    inner_avoiding_transition_edges.add(transition)
                    inner_avoiding_moves.union(solution_number, target)

    fibers: dict[tuple[int, ...], list[int]] = defaultdict(list)
    for index, coloring in enumerate(solutions):
        word = tuple(coloring[edge] for edge in instance["inner_spokes"])
        fibers[word].append(index)
    good_fibers = {word: members for word, members in fibers.items() if is_good_word(word)}

    good_fiber_rows = []
    for word, members in sorted(good_fibers.items()):
        sizes = class_sizes(inner_avoiding_moves, members)
        good_fiber_rows.append(
            {
                "inner_word": "".join(map(str, word)),
                "coloring_count": len(members),
                "inner_avoiding_class_count": len(sizes),
                "inner_avoiding_class_sizes": sizes,
            }
        )

    full_sizes = class_sizes(full_moves, range(len(solutions)))
    good_size_histogram = Counter(
        row["coloring_count"] for row in good_fiber_rows
    )
    good_class_histogram = Counter(
        row["inner_avoiding_class_count"] for row in good_fiber_rows
    )
    return {
        "schema": SCHEMA,
        "algorithm": "explicit-bichromatic-components-and-union-find-v1",
        "graph": name,
        "graph_hash": instance["graph_hash"],
        "solution_count": len(solutions),
        "full_kempe_transition_count": len(full_transition_edges),
        "full_kempe_class_count": len(full_sizes),
        "full_kempe_class_sizes": full_sizes,
        "inner_avoiding_transition_count": len(inner_avoiding_transition_edges),
        "inner_word_fiber_count": len(fibers),
        "good_inner_word_fiber_count": len(good_fibers),
        "good_fiber_size_histogram": {
            str(size): count for size, count in sorted(good_size_histogram.items())
        },
        "good_fiber_class_count_histogram": {
            str(size): count for size, count in sorted(good_class_histogram.items())
        },
        "all_good_fibers_inner_avoiding_connected": all(
            row["inner_avoiding_class_count"] == 1 for row in good_fiber_rows
        ),
        "good_fibers": good_fiber_rows,
    }


def main() -> int:
    args = parse_args()
    names = ("C30", "C40") if args.graph == "all" else (args.graph,)
    for name in names:
        result = analyze_graph(name)
        output = args.output_dir / f"{name.lower()}_annular_kempe.json"
        atomic_write_json(output, result)
        print(
            f"{name}: {result['solution_count']} colorings, "
            f"{result['full_kempe_class_count']} free class, "
            f"{result['good_inner_word_fiber_count']} good fibers, "
            f"connected={result['all_good_fibers_inner_avoiding_connected']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
