#!/usr/bin/env python3
"""Gate-1 composite LKR_in audit for tau/mirror-tau chains.

This is the decisive finite test for the obstruction found at Goertzel
Lemma 8.18: the manuscript's pointwise downstream preparation fails, but the
composite fixed-input Kempe graph may still be connected.  We therefore test
the composite graph directly for every length-2 and length-3 word over the
canonical three-cell gadget and its ordered-stub mirror.
"""

from __future__ import annotations

from collections import Counter, deque
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import argparse
import json
import os
from typing import Iterable

from lemma814_lkr_in_lab import (
    COLOR_PAIRS,
    COLORS,
    TAU,
    Gadget,
    component,
    edge_adjacency,
    kempe_neighbors,
    proper_states,
    switch_on_component,
)


TAU_INPUT_ORDER = ("B0", "B1", "B2", "B3")
TAU_OUTPUT_ORDER = ("B4", "B5", "B6", "B7")


@dataclass(frozen=True)
class GadgetType:
    name: str
    input_order: tuple[str, ...]
    output_order: tuple[str, ...]


TAU_TYPE = GadgetType("tau", TAU_INPUT_ORDER, TAU_OUTPUT_ORDER)
MIRROR_TAU_TYPE = GadgetType(
    "mirror_tau",
    tuple(reversed(TAU_INPUT_ORDER)),
    tuple(reversed(TAU_OUTPUT_ORDER)),
)
GADGET_TYPES = (TAU_TYPE, MIRROR_TAU_TYPE)


def prefixed(i: int, x: str) -> str:
    return f"g{i}:{x}"


def local_color(state: tuple[str, ...], edge: str) -> str:
    return state[TAU.edge_index[edge]]


def stub_internal_endpoint(stub: str) -> str:
    u, v = TAU.endpoints[stub]
    if u in TAU.internal_vertices:
        return u
    if v in TAU.internal_vertices:
        return v
    raise AssertionError(f"stub has no internal endpoint: {stub}")


def is_stub(edge: str) -> bool:
    return edge.startswith("B")


@dataclass(frozen=True)
class CompositeModel:
    gadget: Gadget
    edge_sources: tuple[tuple[int, str], ...]
    output_edges: tuple[str, ...]
    interface_edges: tuple[str, ...]
    closing_edges: tuple[str, ...] = ()


def build_composite_model(word: tuple[GadgetType, ...]) -> CompositeModel:
    edges: list[str] = []
    endpoints: dict[str, tuple[str, str]] = {}
    edge_sources: list[tuple[int, str]] = []
    interface_edges: list[str] = []
    output_edges: list[str] = []

    def add_edge(name: str, endpoint_pair: tuple[str, str], source: tuple[int, str]) -> None:
        edges.append(name)
        endpoints[name] = endpoint_pair
        edge_sources.append(source)

    for i, typ in enumerate(word):
        for edge in TAU.edges:
            if is_stub(edge) and i > 0 and edge in typ.input_order:
                continue
            if is_stub(edge) and i + 1 < len(word) and edge in typ.output_order:
                continue

            u, v = TAU.endpoints[edge]
            name = prefixed(i, edge)
            if edge in typ.input_order and i == 0:
                boundary = f"in{typ.input_order.index(edge)}"
                endpoint_pair = (prefixed(i, stub_internal_endpoint(edge)), boundary)
            elif edge in typ.output_order and i + 1 == len(word):
                boundary = f"out{typ.output_order.index(edge)}"
                endpoint_pair = (prefixed(i, stub_internal_endpoint(edge)), boundary)
                output_edges.append(name)
            else:
                endpoint_pair = (
                    prefixed(i, u) if u in TAU.internal_vertices else prefixed(i, u),
                    prefixed(i, v) if v in TAU.internal_vertices else prefixed(i, v),
                )
            add_edge(name, endpoint_pair, (i, edge))

    for i in range(len(word) - 1):
        left = word[i]
        right = word[i + 1]
        for k, (out_stub, in_stub) in enumerate(zip(left.output_order, right.input_order)):
            name = f"I{i}_{k}:{out_stub}={in_stub}"
            endpoint_pair = (
                prefixed(i, stub_internal_endpoint(out_stub)),
                prefixed(i + 1, stub_internal_endpoint(in_stub)),
            )
            add_edge(name, endpoint_pair, (i, out_stub))
            interface_edges.append(name)

    internal_vertices = tuple(
        prefixed(i, v) for i in range(len(word)) for v in TAU.internal_vertices
    )
    inputs = tuple(prefixed(0, edge) for edge in word[0].input_order)
    name = "_then_".join(typ.name for typ in word)
    return CompositeModel(
        gadget=Gadget(
            name=name,
            edges=tuple(edges),
            endpoints=endpoints,
            internal_vertices=internal_vertices,
            inputs=inputs,
        ),
        edge_sources=tuple(edge_sources),
        output_edges=tuple(output_edges),
        interface_edges=tuple(interface_edges),
    )


def build_closed_collar_model(word: tuple[GadgetType, ...]) -> CompositeModel:
    if len(word) < 2:
        raise ValueError("closed collar L1 audit uses length at least 2")

    edges: list[str] = []
    endpoints: dict[str, tuple[str, str]] = {}
    edge_sources: list[tuple[int, str]] = []
    interface_edges: list[str] = []
    closing_edges: list[str] = []

    def add_edge(name: str, endpoint_pair: tuple[str, str], source: tuple[int, str]) -> None:
        edges.append(name)
        endpoints[name] = endpoint_pair
        edge_sources.append(source)

    for i, typ in enumerate(word):
        for edge in TAU.edges:
            if is_stub(edge) and (edge in typ.input_order or edge in typ.output_order):
                continue

            u, v = TAU.endpoints[edge]
            name = prefixed(i, edge)
            endpoint_pair = (
                prefixed(i, u) if u in TAU.internal_vertices else prefixed(i, u),
                prefixed(i, v) if v in TAU.internal_vertices else prefixed(i, v),
            )
            add_edge(name, endpoint_pair, (i, edge))

    for i in range(len(word) - 1):
        left = word[i]
        right = word[i + 1]
        for k, (out_stub, in_stub) in enumerate(zip(left.output_order, right.input_order)):
            name = f"I{i}_{k}:{out_stub}={in_stub}"
            endpoint_pair = (
                prefixed(i, stub_internal_endpoint(out_stub)),
                prefixed(i + 1, stub_internal_endpoint(in_stub)),
            )
            add_edge(name, endpoint_pair, (i, out_stub))
            interface_edges.append(name)

    last = word[-1]
    first = word[0]
    last_index = len(word) - 1
    for k, (out_stub, in_stub) in enumerate(zip(last.output_order, first.input_order)):
        name = f"C{k}:{out_stub}={in_stub}"
        endpoint_pair = (
            prefixed(last_index, stub_internal_endpoint(out_stub)),
            prefixed(0, stub_internal_endpoint(in_stub)),
        )
        add_edge(name, endpoint_pair, (last_index, out_stub))
        closing_edges.append(name)

    internal_vertices = tuple(
        prefixed(i, v) for i in range(len(word)) for v in TAU.internal_vertices
    )
    name = "closed_" + "_then_".join(typ.name for typ in word)
    return CompositeModel(
        gadget=Gadget(
            name=name,
            edges=tuple(edges),
            endpoints=endpoints,
            internal_vertices=internal_vertices,
            inputs=tuple(closing_edges),
        ),
        edge_sources=tuple(edge_sources),
        output_edges=(),
        interface_edges=tuple(interface_edges),
        closing_edges=tuple(closing_edges),
    )


def input_key_for_type(typ: GadgetType, state: tuple[str, ...]) -> tuple[str, ...]:
    return tuple(local_color(state, edge) for edge in typ.input_order)


def output_key_for_type(typ: GadgetType, state: tuple[str, ...]) -> tuple[str, ...]:
    return tuple(local_color(state, edge) for edge in typ.output_order)


def compatible_local_sequences(
    word: tuple[GadgetType, ...],
    tau_states: list[tuple[str, ...]],
) -> list[tuple[tuple[str, ...], ...]]:
    input_groups: dict[tuple[str, ...], dict[tuple[str, ...], list[tuple[str, ...]]]] = {}
    for typ in GADGET_TYPES:
        groups: dict[tuple[str, ...], list[tuple[str, ...]]] = {}
        for state in tau_states:
            groups.setdefault(input_key_for_type(typ, state), []).append(state)
        input_groups[typ.name] = groups

    sequences: list[tuple[tuple[str, ...], ...]] = [(state,) for state in tau_states]
    for typ in word[1:]:
        extended: list[tuple[tuple[str, ...], ...]] = []
        groups = input_groups[typ.name]
        for seq in sequences:
            prev_typ = word[len(seq) - 1]
            needed = output_key_for_type(prev_typ, seq[-1])
            for state in groups.get(needed, []):
                extended.append(seq + (state,))
        sequences = extended
    return sequences


def compatible_closed_local_sequences_for_outer_key(
    word: tuple[GadgetType, ...],
    tau_states: list[tuple[str, ...]],
    fixed_outer_key: tuple[str, ...],
) -> list[tuple[tuple[str, ...], ...]]:
    if not word:
        return []

    input_groups: dict[str, dict[tuple[str, ...], list[tuple[str, ...]]]] = {}
    for typ in GADGET_TYPES:
        groups: dict[tuple[str, ...], list[tuple[str, ...]]] = {}
        for state in tau_states:
            groups.setdefault(input_key_for_type(typ, state), []).append(state)
        input_groups[typ.name] = groups

    sequences: list[tuple[tuple[str, ...], ...]] = [
        (state,)
        for state in input_groups[word[0].name].get(fixed_outer_key, [])
    ]
    for typ in word[1:]:
        extended: list[tuple[tuple[str, ...], ...]] = []
        groups = input_groups[typ.name]
        for seq in sequences:
            prev_typ = word[len(seq) - 1]
            needed = output_key_for_type(prev_typ, seq[-1])
            for state in groups.get(needed, []):
                extended.append(seq + (state,))
        sequences = extended

    return [
        seq for seq in sequences
        if output_key_for_type(word[-1], seq[-1]) == fixed_outer_key
    ]


def global_state_from_sequence(
    model: CompositeModel,
    sequence: tuple[tuple[str, ...], ...],
) -> tuple[str, ...]:
    return tuple(local_color(sequence[i], edge) for i, edge in model.edge_sources)


def connected_components(vertices: list[int], neighbors: list[set[int]]) -> list[list[int]]:
    remaining = set(vertices)
    comps: list[list[int]] = []
    while remaining:
        root = remaining.pop()
        comp = [root]
        todo = deque([root])
        while todo:
            v = todo.popleft()
            for w in neighbors[v]:
                if w in remaining:
                    remaining.remove(w)
                    comp.append(w)
                    todo.append(w)
        comps.append(sorted(comp))
    return comps


def sparse_modular_laplacian_rank(
    vertices: list[int],
    neighbors: list[set[int]],
    prime: int,
) -> int:
    if not vertices:
        return 0
    pos = {v: i for i, v in enumerate(vertices)}
    rows: list[dict[int, int]] = []
    for v in vertices:
        i = pos[v]
        row: dict[int, int] = {}
        for w in neighbors[v]:
            if w in pos:
                row[i] = (row.get(i, 0) + 1) % prime
                j = pos[w]
                row[j] = (row.get(j, 0) - 1) % prime
        rows.append({k: val for k, val in row.items() if val % prime != 0})

    pivots: dict[int, dict[int, int]] = {}
    for row in rows:
        while row:
            pivot = min(row)
            pivot_row = pivots.get(pivot)
            if pivot_row is None:
                inv = pow(row[pivot], prime - 2, prime)
                normalized = {
                    col: (val * inv) % prime
                    for col, val in row.items()
                    if (val * inv) % prime != 0
                }
                pivots[pivot] = normalized
                break
            factor = row[pivot]
            for col, val in pivot_row.items():
                new_val = (row.get(col, 0) - factor * val) % prime
                if new_val:
                    row[col] = new_val
                elif col in row:
                    del row[col]
    return len(pivots)


def input_key(gadget: Gadget, state: tuple[str, ...]) -> tuple[str, ...]:
    idx = gadget.edge_index
    return tuple(state[idx[e]] for e in gadget.inputs)


def kempe_neighbors_avoiding_edges(
    gadget: Gadget,
    states: list[tuple[str, ...]],
    forbidden_edges: Iterable[str],
) -> list[set[int]]:
    idx_by_state = {state: i for i, state in enumerate(states)}
    adj = edge_adjacency(gadget)
    forbidden = set(forbidden_edges)
    out: list[set[int]] = [set() for _ in states]
    for i, state in enumerate(states):
        for pair in COLOR_PAIRS:
            for seed in gadget.edges:
                comp = component(gadget, adj, state, pair, seed)
                if not comp or comp & forbidden:
                    continue
                target = switch_on_component(gadget, state, pair, comp)
                j = idx_by_state.get(target)
                if j is None:
                    raise AssertionError((gadget.name, state, pair, sorted(comp), target))
                if i != j:
                    out[i].add(j)
                    out[j].add(i)
    return out


def audit_composite_word(
    word: tuple[GadgetType, ...],
    tau_states: list[tuple[str, ...]],
    check_rank: bool,
) -> dict[str, object]:
    model = build_composite_model(word)
    sequences = compatible_local_sequences(word, tau_states)
    states = [global_state_from_sequence(model, seq) for seq in sequences]
    deduped = list(dict.fromkeys(states))
    if len(deduped) != len(states):
        raise AssertionError((model.gadget.name, len(states), len(deduped)))
    states = deduped

    neighbors = kempe_neighbors(model.gadget, states)
    groups: dict[tuple[str, ...], list[int]] = {}
    for i, state in enumerate(states):
        groups.setdefault(input_key(model.gadget, state), []).append(i)

    failures = []
    modular_rank_failures = []
    component_hist = Counter()
    size_hist = Counter()
    for key in product(COLORS, repeat=len(model.gadget.inputs)):
        vertices = groups.get(tuple(key), [])
        comps = connected_components(vertices, neighbors)
        component_hist[len(comps)] += 1
        size_hist[len(vertices)] += 1
        connected = len(comps) <= 1
        if not connected:
            failures.append(
                {
                    "input": key,
                    "size": len(vertices),
                    "component_sizes": [len(c) for c in comps],
                    "representative_states": [
                        dict(zip(model.gadget.edges, states[c[0]])) for c in comps[:4]
                    ],
                }
            )
        expected_rank = max(0, len(vertices) - 1)
        if check_rank:
            for prime in (2147483647, 2147483629):
                rank = sparse_modular_laplacian_rank(vertices, neighbors, prime)
                if rank != expected_rank:
                    modular_rank_failures.append(
                        {
                            "input": key,
                            "size": len(vertices),
                            "prime": prime,
                            "rank": rank,
                            "expected_rank": expected_rank,
                        }
                    )
                    break

    undirected_edges = sum(len(ns) for ns in neighbors) // 2
    return {
        "word": [typ.name for typ in word],
        "name": model.gadget.name,
        "length": len(word),
        "edge_count": len(model.gadget.edges),
        "internal_vertex_count": len(model.gadget.internal_vertices),
        "input_edges": list(model.gadget.inputs),
        "output_edges": list(model.output_edges),
        "interface_edges": list(model.interface_edges),
        "proper_colorings": len(states),
        "kempe_adjacency_edges": undirected_edges,
        "input_group_size_histogram": dict(sorted(size_hist.items())),
        "input_component_count_histogram": dict(sorted(component_hist.items())),
        "lkr_in_holds": not failures,
        "lkr_failures": failures,
        "modular_laplacian_rank_cross_check_mode": "checked" if check_rank else "skipped",
        "modular_laplacian_rank_cross_check_holds": (not modular_rank_failures) if check_rank else None,
        "modular_laplacian_rank_failures": modular_rank_failures,
    }


def word_names(word: tuple[GadgetType, ...]) -> tuple[str, ...]:
    return tuple(typ.name for typ in word)


def word_key(word: tuple[GadgetType, ...]) -> str:
    return ",".join(word_names(word))


def fixed_key_id(key: tuple[str, ...]) -> str:
    return "".join(key)


def fiber_connectivity_payload(
    *,
    model: CompositeModel,
    states: list[tuple[str, ...]],
    neighbors: list[set[int]],
    check_rank: bool,
) -> tuple[dict[str, object], bool]:
    vertices = list(range(len(states)))
    comps = connected_components(vertices, neighbors)
    connected = len(comps) <= 1
    undirected_edges = sum(len(ns) for ns in neighbors) // 2

    modular_rank_failures = []
    expected_rank = max(0, len(vertices) - 1)
    if check_rank:
        for prime in (2147483647, 2147483629):
            rank = sparse_modular_laplacian_rank(vertices, neighbors, prime)
            if rank != expected_rank:
                modular_rank_failures.append(
                    {
                        "prime": prime,
                        "rank": rank,
                        "expected_rank": expected_rank,
                    }
                )
                break

    failure_payload = {}
    if not connected:
        failure_payload = {
            "representative_states": [
                dict(zip(model.gadget.edges, states[c[0]])) for c in comps[:4]
            ],
        }

    payload = {
        "proper_colorings": len(states),
        "kempe_adjacency_edges": undirected_edges,
        "component_count": len(comps),
        "component_sizes": [len(c) for c in comps],
        "connected": connected,
        "empty_fiber": len(states) == 0,
        "modular_laplacian_rank_cross_check_mode": "checked" if check_rank else "skipped",
        "modular_laplacian_rank_cross_check_holds": (
            not modular_rank_failures
        ) if check_rank else None,
        "modular_laplacian_rank_failures": modular_rank_failures,
        **failure_payload,
    }
    return payload, connected


def full_interface_edges(model: CompositeModel) -> tuple[str, ...]:
    return tuple(dict.fromkeys(tuple(model.gadget.inputs) + tuple(model.output_edges)))


def closed_collar_full_interface_edges(model: CompositeModel) -> tuple[str, ...]:
    return tuple(dict.fromkeys(tuple(model.interface_edges) + tuple(model.closing_edges)))


def audit_composite_full_interface_fiber(
    word: tuple[GadgetType, ...],
    fixed_input_key: tuple[str, ...],
    tau_states: list[tuple[str, ...]],
    check_rank: bool,
) -> dict[str, object]:
    model = build_composite_model(word)
    sequences = compatible_local_sequences(word, tau_states)
    states = [
        global_state_from_sequence(model, seq)
        for seq in sequences
        if input_key(model.gadget, global_state_from_sequence(model, seq)) == fixed_input_key
    ]
    deduped = list(dict.fromkeys(states))
    if len(deduped) != len(states):
        raise AssertionError((model.gadget.name, fixed_input_key, len(states), len(deduped)))
    states = deduped

    forbidden = full_interface_edges(model)
    neighbors = kempe_neighbors_avoiding_edges(model.gadget, states, forbidden)
    connectivity, _connected = fiber_connectivity_payload(
        model=model,
        states=states,
        neighbors=neighbors,
        check_rank=check_rank,
    )

    return {
        "run_id": f"{word_key(word)}::{fixed_key_id(fixed_input_key)}",
        "word": list(word_names(word)),
        "name": model.gadget.name,
        "length": len(word),
        "fixed_input_key": list(fixed_input_key),
        "fixed_input_edges": list(model.gadget.inputs),
        "blocked_output_edges": list(model.output_edges),
        "blocked_full_interface_edges": list(forbidden),
        "edge_count": len(model.gadget.edges),
        "internal_vertex_count": len(model.gadget.internal_vertices),
        "interface_edges": list(model.interface_edges),
        **connectivity,
    }


def audit_closed_collar_fiber(
    word: tuple[GadgetType, ...],
    fixed_outer_key: tuple[str, ...],
    tau_states: list[tuple[str, ...]],
    check_rank: bool,
) -> dict[str, object]:
    model = build_closed_collar_model(word)
    sequences = compatible_closed_local_sequences_for_outer_key(
        word, tau_states, fixed_outer_key
    )
    states = [global_state_from_sequence(model, seq) for seq in sequences]
    deduped = list(dict.fromkeys(states))
    if len(deduped) != len(states):
        raise AssertionError((model.gadget.name, fixed_outer_key, len(states), len(deduped)))
    states = deduped

    neighbors = kempe_neighbors(model.gadget, states)
    vertices = list(range(len(states)))
    comps = connected_components(vertices, neighbors)
    connected = len(comps) <= 1
    undirected_edges = sum(len(ns) for ns in neighbors) // 2

    modular_rank_failures = []
    expected_rank = max(0, len(vertices) - 1)
    if check_rank:
        for prime in (2147483647, 2147483629):
            rank = sparse_modular_laplacian_rank(vertices, neighbors, prime)
            if rank != expected_rank:
                modular_rank_failures.append(
                    {
                        "prime": prime,
                        "rank": rank,
                        "expected_rank": expected_rank,
                    }
                )
                break

    failure_payload = {}
    if not connected:
        failure_payload = {
            "component_sizes": [len(c) for c in comps],
            "representative_states": [
                dict(zip(model.gadget.edges, states[c[0]])) for c in comps[:4]
            ],
        }

    return {
        "run_id": f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}",
        "word": list(word_names(word)),
        "name": model.gadget.name,
        "length": len(word),
        "fixed_outer_key": list(fixed_outer_key),
        "fixed_outer_edges": list(model.closing_edges),
        "edge_count": len(model.gadget.edges),
        "internal_vertex_count": len(model.gadget.internal_vertices),
        "interface_edges": list(model.interface_edges),
        "proper_colorings": len(states),
        "kempe_adjacency_edges": undirected_edges,
        "component_count": len(comps),
        "component_sizes": [len(c) for c in comps],
        "connected": connected,
        "empty_fiber": len(states) == 0,
        "modular_laplacian_rank_cross_check_mode": "checked" if check_rank else "skipped",
        "modular_laplacian_rank_cross_check_holds": (
            not modular_rank_failures
        ) if check_rank else None,
        "modular_laplacian_rank_failures": modular_rank_failures,
        **failure_payload,
    }


def audit_closed_collar_full_interface_fiber(
    word: tuple[GadgetType, ...],
    fixed_outer_key: tuple[str, ...],
    tau_states: list[tuple[str, ...]],
    check_rank: bool,
) -> dict[str, object]:
    model = build_closed_collar_model(word)
    sequences = compatible_closed_local_sequences_for_outer_key(
        word, tau_states, fixed_outer_key
    )
    states = [global_state_from_sequence(model, seq) for seq in sequences]
    deduped = list(dict.fromkeys(states))
    if len(deduped) != len(states):
        raise AssertionError((model.gadget.name, fixed_outer_key, len(states), len(deduped)))
    states = deduped

    forbidden = closed_collar_full_interface_edges(model)
    neighbors = kempe_neighbors_avoiding_edges(model.gadget, states, forbidden)
    connectivity, _connected = fiber_connectivity_payload(
        model=model,
        states=states,
        neighbors=neighbors,
        check_rank=check_rank,
    )

    return {
        "run_id": f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}",
        "word": list(word_names(word)),
        "name": model.gadget.name,
        "length": len(word),
        "fixed_outer_key": list(fixed_outer_key),
        "fixed_outer_edges": list(model.closing_edges),
        "blocked_interface_edges": list(model.interface_edges),
        "blocked_full_interface_edges": list(forbidden),
        "edge_count": len(model.gadget.edges),
        "internal_vertex_count": len(model.gadget.internal_vertices),
        **connectivity,
    }


def closed_collar_l1_words() -> list[tuple[GadgetType, ...]]:
    return [word for n in (2, 3) for word in words_of_length(n)]


def refresh_closed_collar_summary(report: dict[str, object]) -> None:
    fibers = report.get("fibers", [])
    assert isinstance(fibers, list)
    planned = report.get("planned_fiber_count", 0)
    assert isinstance(planned, int)
    disconnected = [fiber for fiber in fibers if not fiber.get("connected")]
    report["summary"] = {
        "planned_fiber_count": planned,
        "completed_fiber_count": len(fibers),
        "remaining_fiber_count": max(0, planned - len(fibers)),
        "word_count": len({tuple(fiber.get("word", [])) for fiber in fibers}),
        "nonempty_fiber_count": sum(1 for fiber in fibers if not fiber.get("empty_fiber")),
        "empty_fiber_count": sum(1 for fiber in fibers if fiber.get("empty_fiber")),
        "connected_fiber_count": sum(1 for fiber in fibers if fiber.get("connected")),
        "disconnected_fiber_count": len(disconnected),
        "all_completed_fibers_connected": not disconnected,
        "complete": len(fibers) == planned,
        "first_disconnected_run_id": disconnected[0].get("run_id") if disconnected else None,
    }


def refresh_full_interface_summary(report: dict[str, object]) -> None:
    fibers = report.get("fibers", [])
    assert isinstance(fibers, list)
    planned = report.get("planned_fiber_count", 0)
    assert isinstance(planned, int)
    disconnected = [fiber for fiber in fibers if not fiber.get("connected")]
    first = disconnected[0] if disconnected else None
    report["summary"] = {
        "planned_fiber_count": planned,
        "completed_fiber_count": len(fibers),
        "remaining_fiber_count": max(0, planned - len(fibers)),
        "word_count": len({tuple(fiber.get("word", [])) for fiber in fibers}),
        "nonempty_fiber_count": sum(1 for fiber in fibers if not fiber.get("empty_fiber")),
        "empty_fiber_count": sum(1 for fiber in fibers if fiber.get("empty_fiber")),
        "connected_fiber_count": sum(1 for fiber in fibers if fiber.get("connected")),
        "disconnected_fiber_count": len(disconnected),
        "all_completed_fibers_connected": not disconnected,
        "complete": len(fibers) == planned,
        "first_disconnected_run_id": first.get("run_id") if isinstance(first, dict) else None,
        "first_disconnected_component_sizes": (
            first.get("component_sizes") if isinstance(first, dict) else None
        ),
        "verdict": (
            "disconnected"
            if disconnected
            else ("connected" if len(fibers) == planned else "incomplete")
        ),
    }


def new_full_interface_report(
    *,
    schema: str,
    source: str,
    model_payload: dict[str, object],
    tau_state_count: int,
    check_rank: bool,
) -> dict[str, object]:
    words = closed_collar_l1_words()
    planned_fiber_count = sum(3 ** 4 for _ in words)
    report: dict[str, object] = {
        "schema": schema,
        "source": source,
        "model": model_payload,
        "local_tau_state_count": tau_state_count,
        "word_lengths": [2, 3],
        "planned_words": [list(word_names(word)) for word in words],
        "planned_word_count": len(words),
        "planned_fiber_count": planned_fiber_count,
        "rank_cross_check_mode": "sparse_modular_checked" if check_rank else "skipped_fast_l1",
        "fibers": [],
    }
    refresh_full_interface_summary(report)
    return report


def new_closed_collar_report(tau_state_count: int, check_rank: bool) -> dict[str, object]:
    words = closed_collar_l1_words()
    planned_fiber_count = sum(3 ** 4 for _ in words)
    report: dict[str, object] = {
        "schema": "fourcolor-section-9-2-closed-collar-l1-v1",
        "source": "Section 9.2 closed-collar L1 Kempe-connectivity lab",
        "model": {
            "tau_inputs": list(TAU_INPUT_ORDER),
            "tau_outputs": list(TAU_OUTPUT_ORDER),
            "mirror_tau_inputs": list(MIRROR_TAU_TYPE.input_order),
            "mirror_tau_outputs": list(MIRROR_TAU_TYPE.output_order),
            "closed_collar_rule": (
                "compose a length-2 or length-3 word cyclically by identifying "
                "the final ordered output stubs with the first ordered input stubs"
            ),
            "fixed_outer_fiber": (
                "one four-color key on the closing edges is fixed per run; "
                "switches touching those closing edges are blocked"
            ),
            "switch_rule": "single edge-Kempe switch on a two-color component",
        },
        "local_tau_state_count": tau_state_count,
        "word_lengths": [2, 3],
        "planned_words": [list(word_names(word)) for word in words],
        "planned_word_count": len(words),
        "planned_fiber_count": planned_fiber_count,
        "rank_cross_check_mode": "sparse_modular_checked" if check_rank else "skipped_fast_l1",
        "fibers": [],
    }
    refresh_closed_collar_summary(report)
    return report


def new_composite_full_interface_report(tau_state_count: int, check_rank: bool) -> dict[str, object]:
    return new_full_interface_report(
        schema="fourcolor-section-9-2-composite-full-interface-l1-v1",
        source="Section 9.2 length-2/3 per-input full-interface avoidance lab",
        model_payload={
            "tau_inputs": list(TAU_INPUT_ORDER),
            "tau_outputs": list(TAU_OUTPUT_ORDER),
            "mirror_tau_inputs": list(MIRROR_TAU_TYPE.input_order),
            "mirror_tau_outputs": list(MIRROR_TAU_TYPE.output_order),
            "chain_rule": "serial length-2 or length-3 tau/mirror-tau composition",
            "fixed_input_fiber": "one four-color key on the first input stubs is fixed per run",
            "switch_rule": (
                "single edge-Kempe switch on a two-color component disjoint from "
                "both first input stubs and last output stubs"
            ),
        },
        tau_state_count=tau_state_count,
        check_rank=check_rank,
    )


def new_closed_collar_full_interface_report(
    tau_state_count: int,
    check_rank: bool,
) -> dict[str, object]:
    return new_full_interface_report(
        schema="fourcolor-section-9-2-closed-collar-full-interface-l1-v1",
        source="Section 9.2 closed-collar length-2/3 full-interface avoidance lab",
        model_payload={
            "tau_inputs": list(TAU_INPUT_ORDER),
            "tau_outputs": list(TAU_OUTPUT_ORDER),
            "mirror_tau_inputs": list(MIRROR_TAU_TYPE.input_order),
            "mirror_tau_outputs": list(MIRROR_TAU_TYPE.output_order),
            "closed_collar_rule": (
                "compose a length-2 or length-3 word cyclically by identifying "
                "the final ordered output stubs with the first ordered input stubs"
            ),
            "fixed_outer_fiber": "one four-color key on the closing edges is fixed per run",
            "switch_rule": (
                "single edge-Kempe switch on a two-color component disjoint from "
                "every output-stub representative edge, including the closing edges"
            ),
        },
        tau_state_count=tau_state_count,
        check_rank=check_rank,
    )


def write_json_report(path: Path, report: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    os.replace(tmp, path)


def run_closed_collar_l1(
    output: Path | None,
    resume: bool,
    check_rank: bool,
    continue_after_disconnected: bool,
) -> dict[str, object]:
    tau_states = proper_states(TAU)
    if resume and output is not None and output.exists():
        report = json.loads(output.read_text())
        report.setdefault("fibers", [])
        report.setdefault("rank_cross_check_mode", "resumed")
    else:
        report = new_closed_collar_report(len(tau_states), check_rank)

    fibers = report["fibers"]
    assert isinstance(fibers, list)
    done = {fiber.get("run_id") for fiber in fibers if isinstance(fiber, dict)}

    for word in closed_collar_l1_words():
        model = build_closed_collar_model(word)
        for fixed_outer_key in product(COLORS, repeat=len(model.gadget.inputs)):
            key = tuple(fixed_outer_key)
            run_id = f"{word_key(word)}::{fixed_key_id(key)}"
            if run_id in done:
                continue
            fiber = audit_closed_collar_fiber(word, key, tau_states, check_rank)
            fibers.append(fiber)
            done.add(run_id)
            refresh_closed_collar_summary(report)
            if output is not None:
                write_json_report(output, report)
            if not fiber["connected"] and not continue_after_disconnected:
                return report

    refresh_closed_collar_summary(report)
    if output is not None:
        write_json_report(output, report)
    return report


def run_composite_full_interface_l1(
    output: Path | None,
    resume: bool,
    check_rank: bool,
    continue_after_disconnected: bool,
) -> dict[str, object]:
    tau_states = proper_states(TAU)
    if resume and output is not None and output.exists():
        report = json.loads(output.read_text())
        report.setdefault("fibers", [])
        report.setdefault("rank_cross_check_mode", "resumed")
    else:
        report = new_composite_full_interface_report(len(tau_states), check_rank)

    fibers = report["fibers"]
    assert isinstance(fibers, list)
    done = {fiber.get("run_id") for fiber in fibers if isinstance(fiber, dict)}

    for word in closed_collar_l1_words():
        model = build_composite_model(word)
        for fixed_input_key in product(COLORS, repeat=len(model.gadget.inputs)):
            key = tuple(fixed_input_key)
            run_id = f"{word_key(word)}::{fixed_key_id(key)}"
            if run_id in done:
                continue
            fiber = audit_composite_full_interface_fiber(word, key, tau_states, check_rank)
            fibers.append(fiber)
            done.add(run_id)
            refresh_full_interface_summary(report)
            if output is not None:
                write_json_report(output, report)
            if not fiber["connected"] and not continue_after_disconnected:
                return report

    refresh_full_interface_summary(report)
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_full_interface_l1(
    output: Path | None,
    resume: bool,
    check_rank: bool,
    continue_after_disconnected: bool,
) -> dict[str, object]:
    tau_states = proper_states(TAU)
    if resume and output is not None and output.exists():
        report = json.loads(output.read_text())
        report.setdefault("fibers", [])
        report.setdefault("rank_cross_check_mode", "resumed")
    else:
        report = new_closed_collar_full_interface_report(len(tau_states), check_rank)

    fibers = report["fibers"]
    assert isinstance(fibers, list)
    done = {fiber.get("run_id") for fiber in fibers if isinstance(fiber, dict)}

    for word in closed_collar_l1_words():
        model = build_closed_collar_model(word)
        for fixed_outer_key in product(COLORS, repeat=len(model.gadget.inputs)):
            key = tuple(fixed_outer_key)
            run_id = f"{word_key(word)}::{fixed_key_id(key)}"
            if run_id in done:
                continue
            fiber = audit_closed_collar_full_interface_fiber(word, key, tau_states, check_rank)
            fibers.append(fiber)
            done.add(run_id)
            refresh_full_interface_summary(report)
            if output is not None:
                write_json_report(output, report)
            if not fiber["connected"] and not continue_after_disconnected:
                return report

    refresh_full_interface_summary(report)
    if output is not None:
        write_json_report(output, report)
    return report


def words_of_length(n: int) -> Iterable[tuple[GadgetType, ...]]:
    yield from product(GADGET_TYPES, repeat=n)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--rank",
        action="store_true",
        help="also run sparse modular Laplacian rank checks; slower",
    )
    parser.add_argument(
        "--closed-collar-l1",
        action="store_true",
        help="run the section-9.2 length-2/3 closed-collar fixed-outer-fiber lab",
    )
    parser.add_argument(
        "--full-interface-l1",
        action="store_true",
        help="run the length-2/3 per-input lab with both input and output stubs blocked",
    )
    parser.add_argument(
        "--closed-collar-full-interface-l1",
        action="store_true",
        help="run the cyclic length-2/3 closed-collar lab with every output representative blocked",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="write a resumable JSON verdict for --closed-collar-l1",
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help="resume --closed-collar-l1 from --output if it already exists",
    )
    parser.add_argument(
        "--continue-after-disconnected",
        action="store_true",
        help="continue --closed-collar-l1 after the first disconnected fiber",
    )
    args = parser.parse_args()

    if args.closed_collar_l1:
        report = run_closed_collar_l1(
            output=args.output,
            resume=args.resume,
            check_rank=args.rank,
            continue_after_disconnected=args.continue_after_disconnected,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        summary = report.get("summary", {})
        if isinstance(summary, dict) and summary.get("disconnected_fiber_count"):
            raise SystemExit(2)
        return

    if args.full_interface_l1:
        report = run_composite_full_interface_l1(
            output=args.output,
            resume=args.resume,
            check_rank=args.rank,
            continue_after_disconnected=args.continue_after_disconnected,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        summary = report.get("summary", {})
        if isinstance(summary, dict) and summary.get("disconnected_fiber_count"):
            raise SystemExit(2)
        return

    if args.closed_collar_full_interface_l1:
        report = run_closed_collar_full_interface_l1(
            output=args.output,
            resume=args.resume,
            check_rank=args.rank,
            continue_after_disconnected=args.continue_after_disconnected,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        summary = report.get("summary", {})
        if isinstance(summary, dict) and summary.get("disconnected_fiber_count"):
            raise SystemExit(2)
        return

    tau_states = proper_states(TAU)
    audits = [
        audit_composite_word(word, tau_states, check_rank=args.rank)
        for n in (1, 2, 3)
        for word in words_of_length(n)
    ]
    gate1_audits = [audit for audit in audits if audit["length"] in (2, 3)]
    report = {
        "source": "Goertzel Lemma 8.18 Gate-1 direct composite LKR_in audit",
        "model": {
            "tau_inputs": list(TAU_INPUT_ORDER),
            "tau_outputs": list(TAU_OUTPUT_ORDER),
            "mirror_tau_inputs": list(MIRROR_TAU_TYPE.input_order),
            "mirror_tau_outputs": list(MIRROR_TAU_TYPE.output_order),
            "mirror_model": "same incidence tree with reversed ordered input/output stubs",
            "switch_rule": (
                "single edge-Kempe switch on a two-color component disjoint from "
                "the outer input stub edges"
            ),
        },
        "local_tau_state_count": len(tau_states),
        "audits": audits,
        "gate1_lengths": [2, 3],
        "gate1_word_count": len(gate1_audits),
        "gate1_all_composite_lkr_in_holds": all(
            audit["lkr_in_holds"] and (
                audit["modular_laplacian_rank_cross_check_holds"] is not False
            )
            for audit in gate1_audits
        ),
        "rank_cross_check_mode": "sparse_modular_checked" if args.rank else "skipped_fast_gate1",
        "gate1_failures": [
            audit for audit in gate1_audits
            if not audit["lkr_in_holds"] or audit["modular_laplacian_rank_cross_check_holds"] is False
        ],
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
