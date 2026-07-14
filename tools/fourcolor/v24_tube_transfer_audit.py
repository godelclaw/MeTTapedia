#!/usr/bin/env python3
"""Independent frontier-state audit of the v24 (5,0)-tube transfer."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from collections import Counter, deque
from pathlib import Path
from typing import Any, Iterator

from v24_annular_census import atomic_write_json, load_json
from v24_tube_seed_census import (
    CANONICAL_GOOD_WORD,
    MAJORITY_PAIR,
    make_tube_annulus,
)


SCHEMA = "fourcolor-v24-tube-transfer-audit-v1"
FRONTIER_TOKEN_BASE = 4

State = tuple[tuple[int, ...], tuple[tuple[int, int], ...]]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Audit the tube's alive-germ Pascal transfer."
    )
    parser.add_argument("--length", type=int, default=30)
    parser.add_argument("--direct-max-length", type=int, default=6)
    parser.add_argument(
        "--direct-results-dir",
        type=Path,
        default=Path("results/fourcolor/v24_tube_seed_census"),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_tube_transfer_audit.json"),
    )
    return parser.parse_args()


def distances_from_inner(instance: dict[str, Any]) -> list[int]:
    edges = [tuple(edge) for edge in instance["tangle_edges"]]
    distances = [-1] * len(instance["dual_triangles"])
    queue = deque(instance["inner_face_vertices"])
    for vertex in queue:
        distances[vertex] = 0
    while queue:
        vertex = queue.popleft()
        for edge_index in instance["incident_edges"][vertex]:
            left, right = edges[edge_index]
            neighbor = right if left == vertex else left
            if distances[neighbor] == -1:
                distances[neighbor] = distances[vertex] + 1
                queue.append(neighbor)
    if any(distance < 0 for distance in distances):
        raise AssertionError("the tube tangle is disconnected")
    return distances


def frontier_edges(
    edges: list[tuple[int, int]], distances: list[int], level: int
) -> tuple[int, ...]:
    return tuple(
        edge_index
        for edge_index, (left, right) in enumerate(edges)
        if (distances[left] <= level) != (distances[right] <= level)
    )


def initial_state(
    instance: dict[str, Any],
    edges: list[tuple[int, int]],
    distances: list[int],
) -> State:
    frontier = frontier_edges(edges, distances, 0)
    if len(frontier) != 5 or set(frontier) != set(instance["inner_spokes"]):
        raise AssertionError("the initial cut is not the five inner spokes")
    position = {edge: index for index, edge in enumerate(frontier)}
    color_by_edge = dict(
        zip(instance["inner_spokes"], CANONICAL_GOOD_WORD, strict=True)
    )
    colors = tuple(color_by_edge[edge] for edge in frontier)
    links = tuple(
        sorted(
            (
                terminal,
                FRONTIER_TOKEN_BASE + position[instance["inner_spokes"][terminal]],
            )
            for terminal, color in enumerate(CANONICAL_GOOD_WORD)
            if color in MAJORITY_PAIR
        )
    )
    return colors, links


class UnionFind:
    def __init__(self) -> None:
        self.parent: dict[tuple[str, int], tuple[str, int]] = {}

    def add(self, item: tuple[str, int]) -> None:
        self.parent.setdefault(item, item)

    def find(self, item: tuple[str, int]) -> tuple[str, int]:
        self.add(item)
        root = item
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[item] != item:
            parent = self.parent[item]
            self.parent[item] = root
            item = parent
        return root

    def union(self, left: tuple[str, int], right: tuple[str, int]) -> None:
        left_root = self.find(left)
        right_root = self.find(right)
        if left_root != right_root:
            self.parent[right_root] = left_root


def local_color_extensions(
    state: State,
    level: int,
    edges: list[tuple[int, int]],
    incidence: list[list[int]],
    distances: list[int],
) -> Iterator[tuple[dict[int, int], tuple[int, ...], tuple[int, ...]]]:
    old_frontier = frontier_edges(edges, distances, level)
    new_frontier = frontier_edges(edges, distances, level + 1)
    if not old_frontier or not new_frontier:
        raise AssertionError("a tube transfer cut has an empty frontier")
    new_vertices = {
        vertex for vertex, distance in enumerate(distances) if distance == level + 1
    }
    if len(new_vertices) != 5:
        raise AssertionError("a tube distance layer does not have five vertices")

    colors, _ = state
    color_by_edge = dict(zip(old_frontier, colors, strict=True))
    used_masks = {vertex: 0 for vertex in new_vertices}
    for edge, color in color_by_edge.items():
        left, right = edges[edge]
        endpoint = right if right in new_vertices else left
        if endpoint not in new_vertices:
            raise AssertionError("an old frontier edge misses the new layer")
        used_masks[endpoint] |= 1 << color

    unknown = {
        edge
        for vertex in new_vertices
        for edge in incidence[vertex]
        if edge not in color_by_edge
    }

    def search(unassigned: set[int]) -> Iterator[dict[int, int]]:
        if not unassigned:
            if any(mask != 0b111 for mask in used_masks.values()):
                return
            yield dict(color_by_edge)
            return

        choices = []
        for edge in unassigned:
            endpoints = [vertex for vertex in edges[edge] if vertex in new_vertices]
            domain = tuple(
                color
                for color in range(3)
                if all(not (used_masks[vertex] & (1 << color)) for vertex in endpoints)
            )
            choices.append((len(domain), edge, endpoints, domain))
        _, edge, endpoints, domain = min(choices)
        remainder = set(unassigned)
        remainder.remove(edge)
        for color in domain:
            color_by_edge[edge] = color
            for vertex in endpoints:
                used_masks[vertex] |= 1 << color
            yield from search(remainder)
            for vertex in endpoints:
                used_masks[vertex] &= ~(1 << color)
            del color_by_edge[edge]

    for coloring in search(unknown):
        yield coloring, old_frontier, new_frontier


def successor_state(
    state: State,
    coloring: dict[int, int],
    old_frontier: tuple[int, ...],
    new_frontier: tuple[int, ...],
    edges: list[tuple[int, int]],
    distances: list[int],
    level: int,
) -> State | None:
    _, links = state
    pair = set(MAJORITY_PAIR)
    old_position = {edge: index for index, edge in enumerate(old_frontier)}
    new_position = {edge: index for index, edge in enumerate(new_frontier)}
    union_find = UnionFind()

    def terminal_node(terminal: int) -> tuple[str, int]:
        return "T", terminal

    def old_node(position: int) -> tuple[str, int]:
        return "O", position

    def new_node(position: int) -> tuple[str, int]:
        return "N", position

    def vertex_node(vertex: int) -> tuple[str, int]:
        return "V", vertex

    for left, right in links:
        left_node = (
            terminal_node(left)
            if left < FRONTIER_TOKEN_BASE
            else old_node(left - FRONTIER_TOKEN_BASE)
        )
        right_node = (
            terminal_node(right)
            if right < FRONTIER_TOKEN_BASE
            else old_node(right - FRONTIER_TOKEN_BASE)
        )
        union_find.union(left_node, right_node)

    for edge in old_frontier:
        if coloring[edge] not in pair:
            continue
        left, right = edges[edge]
        new_vertex = left if distances[left] == level + 1 else right
        union_find.union(old_node(old_position[edge]), vertex_node(new_vertex))

    for edge, color in coloring.items():
        if edge in old_position or color not in pair:
            continue
        left, right = edges[edge]
        endpoints = []
        for vertex in (left, right):
            if distances[vertex] == level + 1:
                endpoints.append(vertex_node(vertex))
            elif edge in new_position:
                endpoints.append(new_node(new_position[edge]))
        if len(endpoints) != 2:
            raise AssertionError("a local pair edge has the wrong endpoints")
        union_find.union(endpoints[0], endpoints[1])

    external = [terminal_node(terminal) for terminal in range(4)]
    external.extend(
        new_node(position)
        for position, edge in enumerate(new_frontier)
        if coloring[edge] in pair
    )
    by_component: dict[tuple[str, int], list[tuple[str, int]]] = {}
    for endpoint in external:
        root = union_find.find(endpoint)
        by_component.setdefault(root, []).append(endpoint)

    new_links = []
    for endpoints in by_component.values():
        if len(endpoints) != 2:
            return None
        encoded = []
        for kind, index in endpoints:
            encoded.append(
                index if kind == "T" else FRONTIER_TOKEN_BASE + index
            )
        encoded.sort()
        if encoded[1] < FRONTIER_TOKEN_BASE:
            return None
        new_links.append(tuple(encoded))
    flattened = {token for link in new_links for token in link}
    if not set(range(4)) <= flattened:
        return None
    new_colors = tuple(coloring[edge] for edge in new_frontier)
    return new_colors, tuple(sorted(new_links))


def state_successors(
    state: State,
    level: int,
    edges: list[tuple[int, int]],
    incidence: list[list[int]],
    distances: list[int],
) -> Counter[State]:
    result: Counter[State] = Counter()
    for coloring, old_frontier, new_frontier in local_color_extensions(
        state, level, edges, incidence, distances
    ):
        successor = successor_state(
            state,
            coloring,
            old_frontier,
            new_frontier,
            edges,
            distances,
            level,
        )
        if successor is not None:
            result[successor] += 1
    return result


def state_digest(state: State) -> str:
    payload = json.dumps(state, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def compose_transitions(
    first: dict[State, Counter[State]],
    second: dict[State, Counter[State]],
) -> dict[State, Counter[State]]:
    result = {}
    for source, middle_counts in first.items():
        targets: Counter[State] = Counter()
        for middle, left_count in middle_counts.items():
            for target, right_count in second[middle].items():
                targets[target] += left_count * right_count
        result[source] = targets
    return result


def pascal_chain_order(
    transition: dict[State, Counter[State]],
) -> tuple[list[State], list[State]]:
    if any(sum(targets.values()) != 2 for targets in transition.values()):
        raise AssertionError("a Pascal source does not have extension mass two")
    if any(
        len(targets) != 2 or set(targets.values()) != {1}
        for targets in transition.values()
    ):
        raise AssertionError("a Pascal source does not reach two distinct targets")
    reverse: dict[State, set[State]] = {}
    for source, targets in transition.items():
        for target in targets:
            reverse.setdefault(target, set()).add(source)
    endpoints = sorted(
        (target for target, sources in reverse.items() if len(sources) == 1),
        key=state_digest,
    )
    if len(reverse) != len(transition) + 1 or len(endpoints) != 2:
        raise AssertionError(
            "the Pascal incidence graph is not a path "
            f"(sources={len(transition)}, targets={len(reverse)}, "
            f"target-degree histogram={dict(sorted(Counter(map(len, reverse.values())).items()))})"
        )

    target_order = [endpoints[0]]
    source_order = []
    used_sources: set[State] = set()
    while len(source_order) < len(transition):
        current = target_order[-1]
        choices = reverse[current] - used_sources
        if len(choices) != 1:
            raise AssertionError("the Pascal path traversal is ambiguous")
        source = next(iter(choices))
        used_sources.add(source)
        source_order.append(source)
        next_targets = set(transition[source]) - {current}
        if len(next_targets) != 1:
            raise AssertionError("a Pascal source does not advance along the path")
        target_order.append(next(iter(next_targets)))
    return source_order, target_order


def cycle_order(
    transition: dict[State, Counter[State]],
) -> tuple[list[State], list[State]]:
    reverse: dict[State, set[State]] = {}
    for source, targets in transition.items():
        if len(targets) != 2 or set(targets.values()) != {1}:
            raise AssertionError("a recurrent source does not have two unit arcs")
        for target in targets:
            reverse.setdefault(target, set()).add(source)
    if len(reverse) != len(transition) or any(
        len(sources) != 2 for sources in reverse.values()
    ):
        raise AssertionError("the recurrent incidence graph is not 2-regular")

    start = min(reverse, key=state_digest)
    first_source = min(reverse[start], key=state_digest)
    target_order = [start]
    source_order = []
    current_target = start
    current_source = first_source
    while True:
        source_order.append(current_source)
        next_targets = set(transition[current_source]) - {current_target}
        if len(next_targets) != 1:
            raise AssertionError("the recurrent incidence walk branched")
        next_target = next(iter(next_targets))
        if next_target == start:
            break
        if next_target in target_order:
            raise AssertionError("the recurrent incidence walk closed early")
        target_order.append(next_target)
        next_sources = reverse[next_target] - {current_source}
        if len(next_sources) != 1:
            raise AssertionError("the recurrent incidence walk has a spur")
        current_target = next_target
        current_source = next(iter(next_sources))
    if len(source_order) != len(transition) or len(target_order) != len(reverse):
        raise AssertionError("the recurrent incidence graph is disconnected")
    return source_order, target_order


def transition_signature(transition: dict[State, Counter[State]]) -> str:
    rows = sorted(
        (
            state_digest(source),
            sorted(
                (state_digest(target), count)
                for target, count in targets.items()
            ),
        )
        for source, targets in transition.items()
    )
    payload = json.dumps(rows, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def run_transfer(length: int) -> dict[str, Any]:
    instance = make_tube_annulus(length)
    edges = [tuple(edge) for edge in instance["tangle_edges"]]
    distances = distances_from_inner(instance)
    maximum_distance = max(distances)
    state_counts: dict[int, Counter[State]] = {
        0: Counter({initial_state(instance, edges, distances): 1})
    }
    transitions: dict[int, dict[State, Counter[State]]] = {}
    for level in range(maximum_distance - 1):
        transition = {
            state: state_successors(
                state,
                level,
                edges,
                instance["incident_edges"],
                distances,
            )
            for state in state_counts[level]
        }
        transitions[level] = transition
        next_counts: Counter[State] = Counter()
        for state, multiplicity in state_counts[level].items():
            for successor, local_count in transition[state].items():
                next_counts[successor] += multiplicity * local_count
        state_counts[level + 1] = next_counts

    ring_audits = []
    for level in range(0, maximum_distance - 2, 2):
        composed = compose_transitions(
            transitions[level], transitions[level + 1]
        )
        source_extension_masses = [
            sum(targets.values()) for targets in composed.values()
        ]
        source_distinct_outdegrees = [
            len(targets) for targets in composed.values()
        ]
        every_source_has_two_unit_extensions = all(
            len(targets) == 2 and set(targets.values()) == {1}
            for targets in composed.values()
        )
        incidence_kind = "other"
        try:
            source_order, target_order = pascal_chain_order(composed)
            incidence_kind = "pascal_path"
        except AssertionError:
            source_order, target_order = cycle_order(composed)
            incidence_kind = "recurrent_cycle"
        source_multiplicities = [
            state_counts[level][state] for state in source_order
        ]
        target_multiplicities = [
            state_counts[level + 2][state] for state in target_order
        ]
        source_row = [
            math.comb(len(source_order) - 1, index)
            for index in range(len(source_order))
        ]
        target_row = [
            math.comb(len(source_order), index)
            for index in range(len(target_order))
        ]
        source_is_binomial = source_multiplicities == source_row
        target_is_binomial = target_multiplicities == target_row
        if incidence_kind == "pascal_path" and not (
            source_is_binomial and target_is_binomial
        ):
            raise AssertionError("a Pascal path does not carry Pascal mass")
        adjacency = (
            [[index, index + 1] for index in range(len(source_order))]
            if incidence_kind == "pascal_path"
            else [
                [index, (index + 1) % len(target_order)]
                for index in range(len(source_order))
            ]
        )
        ring_audits.append(
            {
                "source_level": level,
                "target_level": level + 2,
                "source_state_count": len(source_order),
                "target_state_count": len(target_order),
                "source_total_mass": sum(source_multiplicities),
                "target_total_mass": sum(target_multiplicities),
                "incidence_kind": incidence_kind,
                "source_multiplicities": source_multiplicities,
                "target_multiplicities": target_multiplicities,
                "source_is_binomial_row": source_is_binomial,
                "target_is_binomial_row": target_is_binomial,
                "source_state_digests": [state_digest(state) for state in source_order],
                "target_state_digests": [state_digest(state) for state in target_order],
                "every_source_has_two_unit_extensions": (
                    every_source_has_two_unit_extensions
                ),
                "source_extension_masses": source_extension_masses,
                "source_distinct_outdegrees": source_distinct_outdegrees,
                "incidence_adjacency": adjacency,
                "source_state_set_digest": hashlib.sha256(
                    "".join(sorted(map(state_digest, state_counts[level]))).encode()
                ).hexdigest(),
                "target_state_set_digest": hashlib.sha256(
                    "".join(
                        sorted(map(state_digest, state_counts[level + 2]))
                    ).encode()
                ).hexdigest(),
                "transition_signature": transition_signature(composed),
            }
        )

    final_level = maximum_distance - 1
    first_non_pascal_level = next(
        (
            row["source_level"]
            for row in ring_audits
            if row["incidence_kind"] != "pascal_path"
        ),
        None,
    )
    if not all(
        row["every_source_has_two_unit_extensions"] for row in ring_audits
    ):
        raise AssertionError("a reachable alive state lacks binary continuation")
    if sum(state_counts[final_level].values()) != 1 << (length + 1):
        raise AssertionError("the long-tube alive mass does not double per ring")
    return {
        "tube_length": length,
        "graph_hash": instance["graph_hash"],
        "maximum_vertex_distance": maximum_distance,
        "final_frontier_level": final_level,
        "final_alive_state_count": len(state_counts[final_level]),
        "final_alive_mass": sum(state_counts[final_level].values()),
        "expected_doubling_mass": 1 << (length + 1),
        "first_non_pascal_source_level": first_non_pascal_level,
        "all_reachable_sources_have_two_unit_extensions": True,
        "level_state_counts": {
            str(level): len(counts) for level, counts in state_counts.items()
        },
        "level_alive_masses": {
            str(level): sum(counts.values()) for level, counts in state_counts.items()
        },
        "ring_audits": ring_audits,
    }


def direct_census_crosschecks(
    transfer: dict[str, Any], results_dir: Path, maximum_length: int
) -> list[dict[str, Any]]:
    rows = []
    audits_by_target = {
        row["target_level"]: row for row in transfer["ring_audits"]
    }
    for length in range(1, maximum_length + 1):
        path = results_dir / f"tube_j{length}_seed_census.json"
        direct = load_json(path)
        target_level = 2 * length + 2
        transfer_mass = audits_by_target[target_level]["target_total_mass"]
        direct_mass = direct["fully_routed_seed_count"]
        rows.append(
            {
                "tube_length": length,
                "target_level": target_level,
                "transfer_alive_mass": transfer_mass,
                "direct_fully_routed_seed_count": direct_mass,
                "counts_equal": transfer_mass == direct_mass,
                "direct_certificate_file": path.name,
                "direct_certificate_sha256": hashlib.sha256(
                    path.read_bytes()
                ).hexdigest(),
            }
        )
    return rows


def capped_family_audit(maximum_length: int) -> dict[str, Any]:
    rows = []
    for length in range(1, maximum_length + 1):
        transfer = run_transfer(length)
        exit_ring = transfer["ring_audits"][-1]
        rows.append(
            {
                "tube_length": length,
                "graph_hash": transfer["graph_hash"],
                "final_alive_state_count": transfer["final_alive_state_count"],
                "final_alive_mass": transfer["final_alive_mass"],
                "expected_doubling_mass": transfer["expected_doubling_mass"],
                "mass_matches_doubling_formula": (
                    transfer["final_alive_mass"]
                    == transfer["expected_doubling_mass"]
                ),
                "exit_source_level": exit_ring["source_level"],
                "exit_incidence_kind": exit_ring["incidence_kind"],
                "exit_transition_signature": exit_ring["transition_signature"],
                "exit_target_state_set_digest": exit_ring[
                    "target_state_set_digest"
                ],
                "all_reachable_sources_have_two_unit_extensions": transfer[
                    "all_reachable_sources_have_two_unit_extensions"
                ],
            }
        )

    stable_from = None
    for candidate in range(1, maximum_length + 1):
        tail = [row for row in rows if row["tube_length"] >= candidate]
        parity_signatures = {
            parity: {
                (
                    row["exit_transition_signature"],
                    row["exit_target_state_set_digest"],
                )
                for row in tail
                if row["tube_length"] % 2 == parity
            }
            for parity in (0, 1)
        }
        if (
            all(len(signatures) <= 1 for signatures in parity_signatures.values())
            and all(row["final_alive_state_count"] == 10 for row in tail)
            and all(row["exit_incidence_kind"] == "recurrent_cycle" for row in tail)
        ):
            stable_from = candidate
            break
    if stable_from is None:
        raise AssertionError("the capped family did not reach its recurrent regime")
    if not all(row["mass_matches_doubling_formula"] for row in rows):
        raise AssertionError("a capped tube violates the doubling formula")
    if not all(
        row["all_reachable_sources_have_two_unit_extensions"] for row in rows
    ):
        raise AssertionError("a capped tube has a dead reachable source")
    return {
        "maximum_tube_length": maximum_length,
        "first_recurrent_length": stable_from,
        "all_masses_match_doubling_formula": True,
        "all_reachable_sources_have_two_unit_extensions": True,
        "rows": rows,
    }


def main() -> int:
    args = parse_args()
    if args.length < 1:
        raise SystemExit("the tube length must be positive")
    if args.direct_max_length < 0 or args.direct_max_length > args.length:
        raise SystemExit("the direct cross-check range must lie inside the tube")
    transfer = run_transfer(args.length)
    crosschecks = direct_census_crosschecks(
        transfer, args.direct_results_dir, args.direct_max_length
    )
    if not all(row["counts_equal"] for row in crosschecks):
        raise AssertionError("the transfer and direct censuses disagree")
    family = capped_family_audit(args.length)
    result = {
        "schema": SCHEMA,
        "algorithm": "local-ring-coloring-and-germ-pairing-dp-v1",
        "fixed_inner_word": "".join(map(str, CANONICAL_GOOD_WORD)),
        "majority_pair": "".join(map(str, MAJORITY_PAIR)),
        "transfer": transfer,
        "capped_family_audit": family,
        "direct_census_crosschecks": crosschecks,
    }
    atomic_write_json(args.output, result)
    print(
        f"j=1..{args.length}: recurrent from j="
        f"{family['first_recurrent_length']}; final alive mass "
        f"{transfer['final_alive_mass']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
