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
from functools import lru_cache
from itertools import combinations, product
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


def sorted_edges_for_model(model: CompositeModel, edges: Iterable[str]) -> list[str]:
    order = model.gadget.edge_index
    return sorted(edges, key=lambda edge: order[edge])


def pair_winding_components(
    model: CompositeModel,
    state: tuple[str, ...],
    pair: tuple[str, str],
    radial_cut_edges: set[str],
) -> list[dict[str, object]]:
    adj = edge_adjacency(model.gadget)
    idx = model.gadget.edge_index
    pair_set = set(pair)
    unused = {edge for edge in model.gadget.edges if state[idx[edge]] in pair_set}
    components: list[dict[str, object]] = []
    while unused:
        seed = min(unused, key=lambda edge: idx[edge])
        comp = set(component(model.gadget, adj, state, pair, seed))
        unused -= comp
        cut_edges = comp & radial_cut_edges
        crossing_count = len(cut_edges)
        components.append(
            {
                "seed": seed,
                "size": len(comp),
                "crossing_count": crossing_count,
                "winding_parity": crossing_count % 2,
                "radial_cut_edges": sorted_edges_for_model(model, cut_edges),
                "component": sorted_edges_for_model(model, comp),
            }
        )
    return components


def closed_collar_state_winding_data(
    model: CompositeModel,
    state: tuple[str, ...],
) -> tuple[tuple[tuple[str, int, int], ...], dict[str, object]]:
    idx = model.gadget.edge_index
    radial_cut_edges = set(model.closing_edges)
    profile: list[tuple[str, int, int]] = []
    pair_payloads: list[dict[str, object]] = []
    for pair in COLOR_PAIRS:
        components = pair_winding_components(model, state, pair, radial_cut_edges)
        winding0 = sum(
            1 for component_payload in components
            if int(component_payload["winding_parity"]) == 0
        )
        winding1 = sum(
            1 for component_payload in components
            if int(component_payload["winding_parity"]) == 1
        )
        pair_name = "".join(pair)
        cut_parity = (
            sum(1 for edge in radial_cut_edges if state[idx[edge]] in set(pair)) % 2
        )
        component_parity_sum = (
            sum(int(component_payload["winding_parity"]) for component_payload in components) % 2
        )
        if cut_parity != component_parity_sum:
            raise AssertionError((model.gadget.name, pair, cut_parity, component_parity_sum))
        profile.append((pair_name, winding0, winding1))
        pair_payloads.append(
            {
                "pair": list(pair),
                "component_count": len(components),
                "winding0_component_count": winding0,
                "winding1_component_count": winding1,
                "aggregate_f2_cut_parity": cut_parity,
                "components": components,
            }
        )
    profile_tuple = tuple(profile)
    payload = {
        "winding_profile": [
            {
                "pair": pair_name,
                "winding0_component_count": winding0,
                "winding1_component_count": winding1,
            }
            for pair_name, winding0, winding1 in profile_tuple
        ],
        "pairs": pair_payloads,
    }
    return profile_tuple, payload


def winding_profile_payload(profile: tuple[tuple[str, int, int], ...]) -> list[dict[str, object]]:
    return [
        {
            "pair": pair_name,
            "winding0_component_count": winding0,
            "winding1_component_count": winding1,
        }
        for pair_name, winding0, winding1 in profile
    ]


def profile_json_key(profile: tuple[tuple[str, int, int], ...]) -> str:
    return json.dumps(winding_profile_payload(profile), sort_keys=True)


def audit_closed_collar_winding_fiber(
    word: tuple[GadgetType, ...],
    fixed_outer_key: tuple[str, ...],
    tau_states: list[tuple[str, ...]],
    include_all_components: bool,
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

    profile_counts: Counter[str] = Counter()
    profile_payloads: dict[str, list[dict[str, object]]] = {}
    first_state_for_profile: dict[str, dict[str, object]] = {}
    state_winding_profiles: list[dict[str, object]] = []
    full_state_payloads: list[dict[str, object]] = []
    for state_index, state in enumerate(states):
        profile, winding_payload = closed_collar_state_winding_data(model, state)
        profile_key = profile_json_key(profile)
        profile_counts[profile_key] += 1
        profile_payloads.setdefault(profile_key, winding_profile_payload(profile))
        state_payload = {
            "state_index": state_index,
            "state": dict(zip(model.gadget.edges, state)),
            **winding_payload,
        }
        state_winding_profiles.append(
            {
                "state_index": state_index,
                "winding_profile": winding_profile_payload(profile),
            }
        )
        if include_all_components:
            full_state_payloads.append(state_payload)
        first_state_for_profile.setdefault(profile_key, state_payload)

    profile_keys = list(profile_counts)
    witness = None
    if len(profile_keys) > 1:
        witness = {
            "profiles": [
                {
                    "state_count": profile_counts[key],
                    "profile": profile_payloads[key],
                    "state": first_state_for_profile[key],
                }
                for key in profile_keys[:2]
            ]
        }

    return {
        "run_id": f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}",
        "word": list(word_names(word)),
        "name": model.gadget.name,
        "length": len(word),
        "fixed_outer_key": list(fixed_outer_key),
        "fixed_outer_edges": list(model.closing_edges),
        "radial_cut_edges": list(model.closing_edges),
        "edge_count": len(model.gadget.edges),
        "internal_vertex_count": len(model.gadget.internal_vertices),
        "interface_edges": list(model.interface_edges),
        "proper_colorings": len(states),
        "empty_fiber": len(states) == 0,
        "winding_profile_count": len(profile_counts),
        "winding_data_boundary_determined": len(profile_counts) <= 1,
        "winding_profile_histogram": [
            {
                "state_count": count,
                "profile": profile_payloads[key],
            }
            for key, count in profile_counts.items()
        ],
        "state_winding_profiles": state_winding_profiles,
        **({"states": full_state_payloads} if include_all_components else {}),
        "first_winding_freedom_witness": witness,
    }


def multigraph_vertices_and_edges(
    model: CompositeModel,
) -> tuple[list[str], list[tuple[str, str, str]]]:
    vertices = sorted({v for endpoints in model.gadget.endpoints.values() for v in endpoints})
    edges = [
        (edge, endpoints[0], endpoints[1])
        for edge, endpoints in model.gadget.endpoints.items()
    ]
    return vertices, edges


def multigraph_connected_after_removing(
    vertices: list[str],
    edges: list[tuple[str, str, str]],
    removed_edges: set[str],
    vertex_subset: set[str] | None = None,
) -> bool:
    active_vertices = set(vertices) if vertex_subset is None else set(vertex_subset)
    if not active_vertices:
        return True
    adj: dict[str, set[str]] = {v: set() for v in active_vertices}
    for edge, u, v in edges:
        if edge in removed_edges or u not in active_vertices or v not in active_vertices:
            continue
        adj[u].add(v)
        adj[v].add(u)
    root = next(iter(active_vertices))
    seen = {root}
    todo = [root]
    while todo:
        current = todo.pop()
        for nxt in adj[current]:
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return seen == active_vertices


def multigraph_component_count(
    vertices: set[str],
    edges: list[tuple[str, str, str]],
) -> int:
    if not vertices:
        return 0
    adj: dict[str, set[str]] = {v: set() for v in vertices}
    for _edge, u, v in edges:
        if u in vertices and v in vertices:
            adj[u].add(v)
            adj[v].add(u)
    remaining = set(vertices)
    count = 0
    while remaining:
        count += 1
        root = remaining.pop()
        todo = [root]
        while todo:
            current = todo.pop()
            for nxt in adj[current]:
                if nxt in remaining:
                    remaining.remove(nxt)
                    todo.append(nxt)
    return count


def multigraph_has_cycle(
    vertices: set[str],
    edges: list[tuple[str, str, str]],
) -> bool:
    if not vertices:
        return False
    internal_edge_count = sum(
        1 for _edge, u, v in edges if u in vertices and v in vertices
    )
    component_count = multigraph_component_count(vertices, edges)
    return internal_edge_count - len(vertices) + component_count > 0


def cyclic_cut_payloads(
    vertices: list[str],
    edges: list[tuple[str, str, str]],
    max_cut_size: int,
) -> list[dict[str, object]]:
    payloads: list[dict[str, object]] = []
    vertex_set = frozenset(vertices)
    seen: set[tuple[str, ...]] = set()
    for size in range(1, len(vertices)):
        for subset_tuple in combinations(vertices, size):
            side = frozenset(subset_tuple)
            other = vertex_set - side
            canonical = min(tuple(sorted(side)), tuple(sorted(other)))
            if canonical in seen:
                continue
            seen.add(canonical)
            cut_edges = [
                edge for edge, u, v in edges if (u in side) != (v in side)
            ]
            if (
                len(cut_edges) <= max_cut_size
                and multigraph_has_cycle(set(side), edges)
                and multigraph_has_cycle(set(other), edges)
            ):
                payloads.append(
                    {
                        "cut_size": len(cut_edges),
                        "side_vertices": sorted(side),
                        "other_side_vertices": sorted(other),
                        "cut_edges": cut_edges,
                    }
                )
    payloads.sort(
        key=lambda payload: (
            int(payload["cut_size"]),
            len(payload["side_vertices"]),
            payload["side_vertices"],
        )
    )
    return payloads


def cyclic_cut_payload_samples(
    vertices: list[str],
    edges: list[tuple[str, str, str]],
    max_cut_size: int,
    sample_limit: int,
) -> list[dict[str, object]]:
    payloads: list[dict[str, object]] = []
    vertex_set = frozenset(vertices)
    seen: set[tuple[str, ...]] = set()
    for size in range(1, len(vertices)):
        for subset_tuple in combinations(vertices, size):
            side = frozenset(subset_tuple)
            other = vertex_set - side
            canonical = min(tuple(sorted(side)), tuple(sorted(other)))
            if canonical in seen:
                continue
            seen.add(canonical)
            cut_edges = [
                edge for edge, u, v in edges if (u in side) != (v in side)
            ]
            if (
                len(cut_edges) <= max_cut_size
                and multigraph_has_cycle(set(side), edges)
                and multigraph_has_cycle(set(other), edges)
            ):
                payloads.append(
                    {
                        "cut_size": len(cut_edges),
                        "side_vertices": sorted(side),
                        "other_side_vertices": sorted(other),
                        "cut_edges": cut_edges,
                    }
                )
                if len(payloads) >= sample_limit:
                    payloads.sort(
                        key=lambda payload: (
                            int(payload["cut_size"]),
                            len(payload["side_vertices"]),
                            payload["side_vertices"],
                        )
                    )
                    return payloads
    payloads.sort(
        key=lambda payload: (
            int(payload["cut_size"]),
            len(payload["side_vertices"]),
            payload["side_vertices"],
        )
    )
    return payloads


def closed_collar_edge_kind(edge: str) -> str:
    if edge.startswith("P"):
        return "patch"
    if edge.startswith("g0:") or edge.startswith("g1:"):
        return "collar"
    if edge.startswith("C"):
        return "closing"
    if edge.startswith("I"):
        return "interface"
    return "other"


def closed_collar_vertex_kind(vertex: str) -> str:
    if vertex.startswith("N"):
        return "patch_internal"
    if vertex.startswith("g0:") or vertex.startswith("g1:"):
        return "collar"
    return "other"


def closed_collar_cut_shape_payload(
    cut: dict[str, object],
) -> dict[str, object]:
    cut_edges = [str(edge) for edge in cut.get("cut_edges", [])]
    side_vertices = [str(vertex) for vertex in cut.get("side_vertices", [])]
    other_vertices = [str(vertex) for vertex in cut.get("other_side_vertices", [])]
    edge_kind_counter = Counter(closed_collar_edge_kind(edge) for edge in cut_edges)
    side_kind_counter = Counter(closed_collar_vertex_kind(vertex) for vertex in side_vertices)
    other_kind_counter = Counter(closed_collar_vertex_kind(vertex) for vertex in other_vertices)
    return {
        "cut_size": int(cut["cut_size"]),
        "side_vertex_count": len(side_vertices),
        "other_side_vertex_count": len(other_vertices),
        "edge_kind_histogram": dict(sorted(edge_kind_counter.items())),
        "side_vertex_kind_histogram": dict(sorted(side_kind_counter.items())),
        "other_side_vertex_kind_histogram": dict(sorted(other_kind_counter.items())),
        "cut_edges": cut_edges,
        "side_vertices": side_vertices,
    }


def closed_collar_cut_shape_key(
    cut: dict[str, object],
) -> str:
    payload = closed_collar_cut_shape_payload(cut)

    def counts_key(histogram: dict[str, object]) -> str:
        return ",".join(
            f"{key}:{histogram[key]}"
            for key in sorted(histogram)
        )

    return "|".join(
        (
            f"cut:{payload['cut_size']}",
            f"side:{payload['side_vertex_count']}",
            f"edges:{counts_key(payload['edge_kind_histogram'])}",
            f"sideKinds:{counts_key(payload['side_vertex_kind_histogram'])}",
        )
    )


EXACT_DIAGONAL_COLLAR_TWO_POLE_TEMPLATE_KEYS = frozenset(
    (
        "edges:g0:F1F0,g1:F4F5|sideCollar:g0:F1,g1:F5",
        "edges:g0:F4F5,g1:F1F0|sideCollar:g0:F5,g1:F1",
    )
)


def closed_collar_cut_template_key(
    cut: dict[str, object],
) -> str:
    payload = closed_collar_cut_shape_payload(cut)
    cut_edges_key = ",".join(sorted(str(edge) for edge in payload["cut_edges"]))
    side_collar_vertices = sorted(
        str(vertex)
        for vertex in payload["side_vertices"]
        if closed_collar_vertex_kind(str(vertex)) == "collar"
    )
    side_collar_key = ",".join(side_collar_vertices)
    return f"edges:{cut_edges_key}|sideCollar:{side_collar_key}"


def closed_collar_cut_is_exact_diagonal_template(
    cut: dict[str, object],
) -> bool:
    return closed_collar_cut_template_key(cut) in EXACT_DIAGONAL_COLLAR_TWO_POLE_TEMPLATE_KEYS


def first_matching_cyclic_cut_payload(
    vertices: list[str],
    edges: list[tuple[str, str, str]],
    max_cut_size: int,
    predicate,
) -> dict[str, object] | None:
    vertex_set = frozenset(vertices)
    seen: set[tuple[str, ...]] = set()
    for size in range(1, len(vertices)):
        for subset_tuple in combinations(vertices, size):
            side = frozenset(subset_tuple)
            other = vertex_set - side
            canonical = min(tuple(sorted(side)), tuple(sorted(other)))
            if canonical in seen:
                continue
            seen.add(canonical)
            cut_edges = [
                edge for edge, u, v in edges if (u in side) != (v in side)
            ]
            if (
                len(cut_edges) <= max_cut_size
                and multigraph_has_cycle(set(side), edges)
                and multigraph_has_cycle(set(other), edges)
            ):
                payload = {
                    "cut_size": len(cut_edges),
                    "side_vertices": sorted(side),
                    "other_side_vertices": sorted(other),
                    "cut_edges": cut_edges,
                }
                if predicate(payload):
                    return payload
    return None


def literal_cycle_side(
    side: set[str],
    edges: list[tuple[str, str, str]],
) -> bool:
    if len(side) != 5:
        return False
    internal_edges = [
        (edge, u, v) for edge, u, v in edges if u in side and v in side
    ]
    if len(internal_edges) != 5:
        return False
    degree = {v: 0 for v in side}
    for _edge, u, v in internal_edges:
        degree[u] += 1
        degree[v] += 1
    return all(count == 2 for count in degree.values()) and multigraph_connected_after_removing(
        sorted(side), internal_edges, set()
    )


def cap5_like_payloads(
    vertices: list[str],
    edges: list[tuple[str, str, str]],
) -> list[dict[str, object]]:
    payloads: list[dict[str, object]] = []
    vertex_set = frozenset(vertices)
    for subset_tuple in combinations(vertices, 5):
        side = frozenset(subset_tuple)
        other = vertex_set - side
        cut_edges = [edge for edge, u, v in edges if (u in side) != (v in side)]
        if (
            len(cut_edges) == 5
            and literal_cycle_side(set(side), edges)
            and multigraph_has_cycle(set(other), edges)
        ):
            payloads.append(
                {
                    "cap_vertices": sorted(side),
                    "outside_vertices": sorted(other),
                    "boundary_edges": cut_edges,
                }
            )
    payloads.sort(key=lambda payload: payload["cap_vertices"])
    return payloads


def closed_collar_multigraph_audit(model: CompositeModel) -> dict[str, object]:
    vertices, edges = multigraph_vertices_and_edges(model)
    endpoint_pair_buckets: dict[tuple[str, str], list[str]] = {}
    degree = {vertex: 0 for vertex in vertices}
    loop_edges: list[str] = []
    for edge, u, v in edges:
        endpoint_pair = tuple(sorted((u, v)))
        endpoint_pair_buckets.setdefault(endpoint_pair, []).append(edge)
        degree[u] += 1
        degree[v] += 1
        if u == v:
            loop_edges.append(edge)
    parallel_bundles = [
        {
            "endpoints": list(endpoint_pair),
            "edges": edge_names,
        }
        for endpoint_pair, edge_names in sorted(endpoint_pair_buckets.items())
        if len(edge_names) > 1
    ]
    bridges = [
        edge for edge, _u, _v in edges
        if not multigraph_connected_after_removing(vertices, edges, {edge})
    ]
    small_cuts = cyclic_cut_payloads(vertices, edges, 4)
    cap5_like = cap5_like_payloads(vertices, edges)

    planar_payload: dict[str, object]
    try:
        import networkx as nx

        graph = nx.MultiGraph()
        graph.add_nodes_from(vertices)
        for edge, u, v in edges:
            graph.add_edge(u, v, key=edge)
        planar_payload = {
            "checked": True,
            "planar_multigraph": bool(nx.check_planarity(graph)[0]),
        }
    except Exception as exc:  # pragma: no cover - environment fallback
        planar_payload = {
            "checked": False,
            "planar_multigraph": None,
            "error": repr(exc),
        }

    connected = multigraph_connected_after_removing(vertices, edges, set())
    cubic = all(count == 3 for count in degree.values())
    simple_endpoint_realization = not loop_edges and not parallel_bundles
    no_small_cyclic_cut_le4 = not small_cuts
    cap5_free_literal_cycle_test = not cap5_like
    planar_ok = planar_payload.get("planar_multigraph") is True

    normal_form_tests = [
        {
            "name": "connected_multigraph",
            "passes": connected,
            "evidence": {"vertex_count": len(vertices), "edge_count": len(edges)},
        },
        {
            "name": "cubic_multigraph",
            "passes": cubic,
            "evidence": {"degrees": degree},
        },
        {
            "name": "bridgeless_multigraph",
            "passes": not bridges,
            "evidence": {"bridges": bridges},
        },
        {
            "name": "planar_multigraph",
            "passes": planar_ok,
            "evidence": planar_payload,
        },
        {
            "name": "simple_endpoint_realization",
            "passes": simple_endpoint_realization,
            "evidence": {
                "loop_edges": loop_edges,
                "parallel_edge_bundles": parallel_bundles,
            },
        },
        {
            "name": "no_cyclic_edge_cut_of_size_at_most_four",
            "passes": no_small_cyclic_cut_le4,
            "evidence": {
                "small_cyclic_cut_count": len(small_cuts),
                "small_cyclic_cuts": small_cuts,
            },
        },
        {
            "name": "cap5_free_literal_five_cycle_test",
            "passes": cap5_free_literal_cycle_test,
            "evidence": {
                "cap5_like_cut_count": len(cap5_like),
                "cap5_like_cuts": cap5_like,
            },
        },
    ]
    first_blocker = next(
        (test for test in normal_form_tests if not bool(test["passes"])),
        None,
    )
    return {
        "vertices": vertices,
        "edges": [
            {"edge": edge, "endpoints": [u, v]} for edge, u, v in edges
        ],
        "vertex_count": len(vertices),
        "edge_count": len(edges),
        "unique_endpoint_pair_count": len(endpoint_pair_buckets),
        "degree": degree,
        "parallel_edge_bundles": parallel_bundles,
        "loop_edges": loop_edges,
        "bridges": bridges,
        "small_cyclic_cuts": small_cuts,
        "cap5_like_cuts": cap5_like,
        "normal_form_tests": normal_form_tests,
        "first_failed_normal_form_test": first_blocker,
    }


def closed_collar_multigraph_prefix_audit(
    model: CompositeModel,
    sample_limit: int,
) -> dict[str, object]:
    vertices, edges = multigraph_vertices_and_edges(model)
    endpoint_pair_buckets: dict[tuple[str, str], list[str]] = {}
    degree = {vertex: 0 for vertex in vertices}
    loop_edges: list[str] = []
    for edge, u, v in edges:
        endpoint_pair = tuple(sorted((u, v)))
        endpoint_pair_buckets.setdefault(endpoint_pair, []).append(edge)
        degree[u] += 1
        degree[v] += 1
        if u == v:
            loop_edges.append(edge)
    parallel_bundles = [
        {
            "endpoints": list(endpoint_pair),
            "edges": edge_names,
        }
        for endpoint_pair, edge_names in sorted(endpoint_pair_buckets.items())
        if len(edge_names) > 1
    ]
    bridges = [
        edge for edge, _u, _v in edges
        if not multigraph_connected_after_removing(vertices, edges, {edge})
    ]
    planar_payload: dict[str, object]
    try:
        import networkx as nx

        graph = nx.MultiGraph()
        graph.add_nodes_from(vertices)
        for edge, u, v in edges:
            graph.add_edge(u, v, key=edge)
        planar_payload = {
            "checked": True,
            "planar_multigraph": bool(nx.check_planarity(graph)[0]),
        }
    except Exception as exc:  # pragma: no cover - environment fallback
        planar_payload = {
            "checked": False,
            "planar_multigraph": None,
            "error": repr(exc),
        }

    connected = multigraph_connected_after_removing(vertices, edges, set())
    cubic = all(count == 3 for count in degree.values())
    simple_endpoint_realization = not loop_edges and not parallel_bundles
    planar_ok = planar_payload.get("planar_multigraph") is True
    small_cuts: list[dict[str, object]] = []
    cap5_like: list[dict[str, object]] = []
    small_cuts_checked = False
    cap5_checked = False

    normal_form_tests = [
        {
            "name": "connected_multigraph",
            "passes": connected,
            "evidence": {"vertex_count": len(vertices), "edge_count": len(edges)},
        },
        {
            "name": "cubic_multigraph",
            "passes": cubic,
            "evidence": {"degrees": degree},
        },
        {
            "name": "bridgeless_multigraph",
            "passes": not bridges,
            "evidence": {"bridges": bridges},
        },
        {
            "name": "planar_multigraph",
            "passes": planar_ok,
            "evidence": planar_payload,
        },
        {
            "name": "simple_endpoint_realization",
            "passes": simple_endpoint_realization,
            "evidence": {
                "loop_edges": loop_edges,
                "parallel_edge_bundles": parallel_bundles,
            },
        },
    ]
    first_blocker = next(
        (test for test in normal_form_tests if not bool(test["passes"])),
        None,
    )
    if first_blocker is None:
        small_cuts_checked = True
        small_cuts = cyclic_cut_payload_samples(vertices, edges, 4, sample_limit)
        normal_form_tests.append(
            {
                "name": "no_cyclic_edge_cut_of_size_at_most_four",
                "passes": not small_cuts,
                "evidence": {
                    "small_cyclic_cut_detected": bool(small_cuts),
                    "small_cyclic_cut_samples": small_cuts,
                },
            }
        )
        first_blocker = next(
            (test for test in normal_form_tests if not bool(test["passes"])),
            None,
        )
    if first_blocker is None:
        cap5_checked = True
        cap5_like = cap5_like_payloads(vertices, edges)
        normal_form_tests.append(
            {
                "name": "cap5_free_literal_five_cycle_test",
                "passes": not cap5_like,
                "evidence": {
                    "cap5_like_cut_count": len(cap5_like),
                    "cap5_like_cuts": cap5_like[:sample_limit],
                },
            }
        )
        first_blocker = next(
            (test for test in normal_form_tests if not bool(test["passes"])),
            None,
        )

    return {
        "vertex_count": len(vertices),
        "edge_count": len(edges),
        "unique_endpoint_pair_count": len(endpoint_pair_buckets),
        "degree": degree,
        "parallel_edge_bundles": parallel_bundles,
        "loop_edges": loop_edges,
        "bridges": bridges,
        "small_cyclic_cuts_checked": small_cuts_checked,
        "small_cyclic_cuts": small_cuts,
        "small_cyclic_cut_sample_count": len(small_cuts),
        "minimum_small_cyclic_cut_size": (
            min(int(cut["cut_size"]) for cut in small_cuts)
            if small_cuts
            else None
        ),
        "cap5_like_cuts_checked": cap5_checked,
        "cap5_like_cuts": cap5_like[:sample_limit],
        "normal_form_tests": normal_form_tests,
        "first_failed_normal_form_test": first_blocker,
    }


def third_color(c0: str, c1: str) -> str:
    remaining = [color for color in COLORS if color not in (c0, c1)]
    if len(remaining) != 1:
        raise ValueError(f"expected two distinct colors, got {c0!r}, {c1!r}")
    return remaining[0]


def proper_state_check(gadget: Gadget, state: tuple[str, ...]) -> dict[str, object]:
    idx = gadget.edge_index
    failures = []
    for vertex, incident_edges in gadget.incident.items():
        colors = [state[idx[edge]] for edge in incident_edges]
        if len(incident_edges) != 3 or len(set(colors)) != len(colors):
            failures.append(
                {
                    "vertex": vertex,
                    "incident_edges": list(incident_edges),
                    "colors": colors,
                }
            )
    return {
        "proper": not failures,
        "failures": failures,
    }


def k4_desingularized_model_and_state(
    model: CompositeModel,
    state: tuple[str, ...],
) -> tuple[CompositeModel, tuple[str, ...], list[dict[str, object]]]:
    idx = model.gadget.edge_index
    endpoint_pair_buckets: dict[tuple[str, str], list[str]] = {}
    for edge, endpoints in model.gadget.endpoints.items():
        endpoint_pair_buckets.setdefault(tuple(sorted(endpoints)), []).append(edge)
    replacement_bundles = {
        endpoint_pair: edge_names
        for endpoint_pair, edge_names in endpoint_pair_buckets.items()
        if len(edge_names) == 2
    }

    new_edges: list[str] = []
    new_endpoints: dict[str, tuple[str, str]] = {}
    new_colors: dict[str, str] = {}
    radial_cut_edges: list[str] = []
    original_radial_cut = set(model.closing_edges)
    replacement_payloads: list[dict[str, object]] = []

    for edge in model.gadget.edges:
        endpoint_pair = tuple(sorted(model.gadget.endpoints[edge]))
        if endpoint_pair in replacement_bundles:
            continue
        new_edges.append(edge)
        new_endpoints[edge] = model.gadget.endpoints[edge]
        new_colors[edge] = state[idx[edge]]
        if edge in original_radial_cut:
            radial_cut_edges.append(edge)

    for bundle_index, (endpoint_pair, edge_names) in enumerate(
        sorted(replacement_bundles.items())
    ):
        e0, e1 = edge_names
        u, v = model.gadget.endpoints[e0]
        a = f"K{bundle_index}:a"
        b = f"K{bundle_index}:b"
        c0 = state[idx[e0]]
        c1 = state[idx[e1]]
        c2 = third_color(c0, c1)
        replacement_edges = [
            (
                f"K{bundle_index}:{e0}:u-a",
                (u, a),
                c0,
                e0 in original_radial_cut,
            ),
            (
                f"K{bundle_index}:{e1}:u-b",
                (u, b),
                c1,
                e1 in original_radial_cut,
            ),
            (
                f"K{bundle_index}:{e1}:v-a",
                (v, a),
                c1,
                False,
            ),
            (
                f"K{bundle_index}:{e0}:v-b",
                (v, b),
                c0,
                False,
            ),
            (
                f"K{bundle_index}:cross",
                (a, b),
                c2,
                False,
            ),
        ]
        for edge, endpoints, color, is_radial in replacement_edges:
            new_edges.append(edge)
            new_endpoints[edge] = endpoints
            new_colors[edge] = color
            if is_radial:
                radial_cut_edges.append(edge)
        replacement_payloads.append(
            {
                "original_endpoint_pair": list(endpoint_pair),
                "original_edges": edge_names,
                "replacement_vertices": [a, b],
                "replacement_edges": [
                    {
                        "edge": edge,
                        "endpoints": list(endpoints),
                        "inherits_radial_cut": is_radial,
                    }
                    for edge, endpoints, _color, is_radial in replacement_edges
                ],
            }
        )

    vertices = sorted({v for endpoints in new_endpoints.values() for v in endpoints})
    gadget = Gadget(
        name=f"{model.gadget.name}_k4_desingularized",
        edges=tuple(new_edges),
        endpoints=new_endpoints,
        internal_vertices=tuple(vertices),
        inputs=tuple(radial_cut_edges),
    )
    desingularized_model = CompositeModel(
        gadget=gadget,
        edge_sources=(),
        output_edges=(),
        interface_edges=(),
        closing_edges=tuple(radial_cut_edges),
    )
    desingularized_state = tuple(new_colors[edge] for edge in new_edges)
    return desingularized_model, desingularized_state, replacement_payloads


def closed_collar_profile_payload_for_model(
    model: CompositeModel,
    state: tuple[str, ...],
) -> list[dict[str, object]]:
    profile, _payload = closed_collar_state_winding_data(model, state)
    return winding_profile_payload(profile)


def winding_profile_key(profile: list[dict[str, object]]) -> str:
    parts: list[str] = []
    for item in profile:
        pair = str(item["pair"])
        winding0 = int(item["winding0_component_count"])
        winding1 = int(item["winding1_component_count"])
        parts.append(f"{pair}:{winding0}/{winding1}")
    return "|".join(parts)


PATCH_TERMINALS = ("A", "B", "C", "D")
PATCH_TERMINAL_VERTICES = {
    "A": "g1:F5",
    "B": "g0:F1",
    "C": "g0:F5",
    "D": "g1:F1",
}
PATCH_REMOVED_PARALLEL_EDGES = frozenset(
    (
        "C1:B5=B1",
        "C2:B6=B2",
        "I0_1:B5=B1",
        "I0_2:B6=B2",
    )
)


def simple_patch_vertices(internal_vertex_count: int) -> tuple[str, ...]:
    return PATCH_TERMINALS + tuple(
        f"N{i}" for i in range(internal_vertex_count)
    )


def simple_patch_degree_target(vertex: str) -> int:
    return 2 if vertex in PATCH_TERMINALS else 3


def iter_simple_patch_edge_sets(
    internal_vertex_count: int,
) -> Iterable[tuple[tuple[str, str], ...]]:
    vertices = simple_patch_vertices(internal_vertex_count)
    degree_target = {vertex: simple_patch_degree_target(vertex) for vertex in vertices}
    if sum(degree_target.values()) % 2:
        return
    candidates = list(combinations(vertices, 2))
    remaining_incidence: list[dict[str, int]] = []
    for start in range(len(candidates) + 1):
        counts = {vertex: 0 for vertex in vertices}
        for u, v in candidates[start:]:
            counts[u] += 1
            counts[v] += 1
        remaining_incidence.append(counts)

    degree = {vertex: 0 for vertex in vertices}
    chosen: list[tuple[str, str]] = []

    def rec(i: int) -> Iterable[tuple[tuple[str, str], ...]]:
        if i == len(candidates):
            if all(degree[v] == degree_target[v] for v in vertices):
                yield tuple(chosen)
            return
        for vertex in vertices:
            if (
                degree[vertex] > degree_target[vertex]
                or degree[vertex] + remaining_incidence[i][vertex] < degree_target[vertex]
            ):
                return

        u, v = candidates[i]
        if degree[u] < degree_target[u] and degree[v] < degree_target[v]:
            chosen.append((u, v))
            degree[u] += 1
            degree[v] += 1
            yield from rec(i + 1)
            degree[u] -= 1
            degree[v] -= 1
            chosen.pop()
        yield from rec(i + 1)

    yield from rec(0)


class SimplePatchIndexer:
    def __init__(self, internal_vertex_count: int) -> None:
        self.vertices = simple_patch_vertices(internal_vertex_count)
        self.degree_target = tuple(
            simple_patch_degree_target(vertex) for vertex in self.vertices
        )
        self.candidates = tuple(combinations(range(len(self.vertices)), 2))
        remaining_incidence: list[tuple[int, ...]] = [
            (0,) * len(self.vertices) for _ in range(len(self.candidates) + 1)
        ]
        running = [0 for _ in self.vertices]
        remaining_incidence[len(self.candidates)] = tuple(running)
        for i in range(len(self.candidates) - 1, -1, -1):
            u, v = self.candidates[i]
            running = list(remaining_incidence[i + 1])
            running[u] += 1
            running[v] += 1
            remaining_incidence[i] = tuple(running)
        self.remaining_incidence = tuple(remaining_incidence)

    @lru_cache(maxsize=None)
    def count_from(self, i: int, remaining: tuple[int, ...]) -> int:
        if i == len(self.candidates):
            return 1 if all(value == 0 for value in remaining) else 0
        available = self.remaining_incidence[i]
        for need, possible in zip(remaining, available):
            if need < 0 or need > possible:
                return 0
        u, v = self.candidates[i]
        total = self.count_from(i + 1, remaining)
        if remaining[u] > 0 and remaining[v] > 0:
            next_remaining = list(remaining)
            next_remaining[u] -= 1
            next_remaining[v] -= 1
            total += self.count_from(i + 1, tuple(next_remaining))
        return total

    def count(self) -> int:
        return self.count_from(0, self.degree_target)

    def edge_set_at_index(self, patch_index: int) -> tuple[tuple[str, str], ...]:
        total_count = self.count()
        if patch_index < 0 or patch_index >= total_count:
            raise ValueError(
                f"patch index {patch_index} is outside [0, {total_count})"
            )

        remaining = self.degree_target
        chosen: list[tuple[str, str]] = []
        index = patch_index
        for i, (u, v) in enumerate(self.candidates):
            include_count = 0
            include_remaining: tuple[int, ...] | None = None
            if remaining[u] > 0 and remaining[v] > 0:
                next_remaining = list(remaining)
                next_remaining[u] -= 1
                next_remaining[v] -= 1
                include_remaining = tuple(next_remaining)
                include_count = self.count_from(i + 1, include_remaining)
            if index < include_count:
                chosen.append((self.vertices[u], self.vertices[v]))
                assert include_remaining is not None
                remaining = include_remaining
            else:
                index -= include_count
        if any(value != 0 for value in remaining):
            raise AssertionError((patch_index, remaining))
        return tuple(chosen)


SIMPLE_PATCH_INDEXERS: dict[int, SimplePatchIndexer] = {}


def simple_patch_indexer(internal_vertex_count: int) -> SimplePatchIndexer:
    if internal_vertex_count < 0 or internal_vertex_count % 2:
        raise ValueError("patch internal vertex count must be a nonnegative even number")
    if internal_vertex_count not in SIMPLE_PATCH_INDEXERS:
        SIMPLE_PATCH_INDEXERS[internal_vertex_count] = SimplePatchIndexer(
            internal_vertex_count
        )
    return SIMPLE_PATCH_INDEXERS[internal_vertex_count]


def simple_patch_edge_set_count(internal_vertex_count: int) -> int:
    return simple_patch_indexer(internal_vertex_count).count()


def simple_patch_edge_set_at_index(
    internal_vertex_count: int,
    patch_index: int,
) -> tuple[tuple[str, str], ...]:
    return simple_patch_indexer(internal_vertex_count).edge_set_at_index(patch_index)


def stratified_patch_indices(total_count: int, sample_count: int) -> tuple[int, ...]:
    if total_count <= 0:
        raise ValueError("total patch count must be positive")
    if sample_count <= 0:
        raise ValueError("stratified sample count must be positive")
    if sample_count == 1:
        return (0,)
    indices = [
        (i * (total_count - 1)) // (sample_count - 1)
        for i in range(sample_count)
    ]
    return tuple(dict.fromkeys(indices))


def parse_patch_index_list(raw: str) -> tuple[int, ...]:
    indices = []
    for part in raw.split(","):
        text = part.strip()
        if not text:
            continue
        indices.append(int(text))
    if not indices:
        raise ValueError("patch index list must contain at least one integer")
    return tuple(dict.fromkeys(indices))


def simple_patch_model(
    base_model: CompositeModel,
    patch_edges: tuple[tuple[str, str], ...],
    radial_order: tuple[str, str] | None = None,
) -> tuple[CompositeModel, tuple[str, ...], tuple[str, str]]:
    edges: list[str] = []
    endpoints: dict[str, tuple[str, str]] = {}

    for edge in base_model.gadget.edges:
        if edge in PATCH_REMOVED_PARALLEL_EDGES:
            continue
        edges.append(edge)
        endpoints[edge] = base_model.gadget.endpoints[edge]

    for i, (u, v) in enumerate(patch_edges):
        edge = f"P{i}:{u}-{v}"
        edges.append(edge)
        endpoints[edge] = (
            PATCH_TERMINAL_VERTICES.get(u, u),
            PATCH_TERMINAL_VERTICES.get(v, v),
        )

    patch_edge_names = tuple(edge for edge in edges if edge.startswith("P"))
    radial_edges = tuple(
        edge
        for edge in patch_edge_names
        if PATCH_TERMINAL_VERTICES["A"] in endpoints[edge]
    )
    if len(radial_edges) != 2:
        raise AssertionError((patch_edges, radial_edges))
    if radial_order is not None:
        radial_edges = radial_order

    vertices = tuple(sorted({vertex for pair in endpoints.values() for vertex in pair}))
    closing_edges = ("C0:B4=B0",) + radial_edges + ("C3:B7=B3",)
    gadget = Gadget(
        name="closed_tau_tau_simple_patch",
        edges=tuple(edges),
        endpoints=endpoints,
        internal_vertices=vertices,
        inputs=closing_edges,
    )
    return (
        CompositeModel(
            gadget=gadget,
            edge_sources=(),
            output_edges=(),
            interface_edges=(),
            closing_edges=closing_edges,
        ),
        patch_edge_names,
        radial_edges,
    )


def simple_patch_profile_preserving_extension(
    model: CompositeModel,
    patch_edge_names: tuple[str, ...],
    radial_edges: tuple[str, str],
    fixed_edge_colors: dict[str, str],
    desired_profile: list[dict[str, object]],
) -> tuple[str, ...] | None:
    colors = dict(fixed_edge_colors)
    for edge, color in zip(radial_edges, ("r", "b")):
        colors[edge] = color

    incident: dict[str, list[str]] = {
        vertex: [] for vertex in model.gadget.internal_vertices
    }
    for edge, (u, v) in model.gadget.endpoints.items():
        incident[u].append(edge)
        incident[v].append(edge)

    def vertex_partial_ok(vertex: str) -> bool:
        seen = [colors[edge] for edge in incident[vertex] if edge in colors]
        return len(seen) == len(set(seen))

    if any(not vertex_partial_ok(vertex) for vertex in incident):
        return None

    unassigned_patch_edges = [edge for edge in patch_edge_names if edge not in colors]
    unassigned_patch_edges.sort(
        key=lambda edge: -sum(
            1
            for vertex in model.gadget.endpoints[edge]
            for incident_edge in incident[vertex]
            if incident_edge in colors
        )
    )

    def rec(i: int) -> tuple[str, ...] | None:
        if i == len(unassigned_patch_edges):
            state = tuple(colors[edge] for edge in model.gadget.edges)
            if not proper_state_check(model.gadget, state)["proper"]:
                return None
            if closed_collar_profile_payload_for_model(model, state) == desired_profile:
                return state
            return None

        edge = unassigned_patch_edges[i]
        u, v = model.gadget.endpoints[edge]
        for color in COLORS:
            colors[edge] = color
            if vertex_partial_ok(u) and vertex_partial_ok(v):
                result = rec(i + 1)
                if result is not None:
                    return result
            del colors[edge]
        return None

    return rec(0)


def simple_patch_profile_extension_diagnostic(
    model: CompositeModel,
    patch_edge_names: tuple[str, ...],
    radial_edges: tuple[str, str],
    fixed_edge_colors: dict[str, str],
    desired_profile: list[dict[str, object]],
) -> dict[str, object]:
    colors = dict(fixed_edge_colors)
    desired_profile_key = winding_profile_key(desired_profile)
    for edge, color in zip(radial_edges, ("r", "b")):
        colors[edge] = color

    incident: dict[str, list[str]] = {
        vertex: [] for vertex in model.gadget.internal_vertices
    }
    for edge, (u, v) in model.gadget.endpoints.items():
        incident[u].append(edge)
        incident[v].append(edge)

    def vertex_partial_ok(vertex: str) -> bool:
        seen = [colors[edge] for edge in incident[vertex] if edge in colors]
        return len(seen) == len(set(seen))

    terminal_conflicts = [
        vertex for vertex in incident if not vertex_partial_ok(vertex)
    ]
    if terminal_conflicts:
        return {
            "profile_failure_kind": "terminal_precolor_conflict",
            "desired_profile_key": desired_profile_key,
            "proper_tait_extension_count": 0,
            "matching_profile_extension_count": 0,
            "profile_variant_count": 0,
            "proper_tait_extension_profile_histogram": {},
            "terminal_precolor_conflict_vertices": terminal_conflicts,
        }

    unassigned_patch_edges = [edge for edge in patch_edge_names if edge not in colors]
    unassigned_patch_edges.sort(
        key=lambda edge: -sum(
            1
            for vertex in model.gadget.endpoints[edge]
            for incident_edge in incident[vertex]
            if incident_edge in colors
        )
    )

    proper_tait_extension_count = 0
    matching_profile_extension_count = 0
    profile_histogram: Counter[str] = Counter()

    def rec(i: int) -> None:
        nonlocal proper_tait_extension_count, matching_profile_extension_count
        if i == len(unassigned_patch_edges):
            state = tuple(colors[edge] for edge in model.gadget.edges)
            if not proper_state_check(model.gadget, state)["proper"]:
                return
            proper_tait_extension_count += 1
            profile = closed_collar_profile_payload_for_model(model, state)
            profile_histogram[winding_profile_key(profile)] += 1
            if profile == desired_profile:
                matching_profile_extension_count += 1
            return

        edge = unassigned_patch_edges[i]
        u, v = model.gadget.endpoints[edge]
        for color in COLORS:
            colors[edge] = color
            if vertex_partial_ok(u) and vertex_partial_ok(v):
                rec(i + 1)
            del colors[edge]

    rec(0)
    if matching_profile_extension_count:
        profile_failure_kind = None
    elif proper_tait_extension_count:
        profile_failure_kind = "proper_extensions_wrong_profile"
    else:
        profile_failure_kind = "no_proper_tait_extension"
    return {
        "profile_failure_kind": profile_failure_kind,
        "desired_profile_key": desired_profile_key,
        "proper_tait_extension_count": proper_tait_extension_count,
        "matching_profile_extension_count": matching_profile_extension_count,
        "profile_variant_count": len(profile_histogram),
        "proper_tait_extension_profile_histogram":
            dict(sorted(profile_histogram.items())),
        "terminal_precolor_conflict_vertices": [],
    }


def audit_closed_collar_winding_simple_patch_search(
    tau_states: list[tuple[str, ...]],
    max_internal_vertices: int,
    sample_limit: int,
) -> dict[str, object]:
    word = (TAU_TYPE, TAU_TYPE)
    fixed_outer_key = ("r", "r", "b", "b")
    base_model = build_closed_collar_model(word)
    base_fiber = audit_closed_collar_winding_fiber(
        word,
        fixed_outer_key,
        tau_states,
        include_all_components=True,
    )
    base_states = base_fiber.get("states", [])
    assert isinstance(base_states, list)

    internal_counts = [
        count for count in range(max_internal_vertices + 1) if count % 2 == 0
    ]
    reports: list[dict[str, object]] = []
    profile_preserving_samples: list[dict[str, object]] = []
    sampled_first_blockers: set[str] = set()
    total_profile_preserving_cases = 0
    total_normal_form_prefix_passing_cases = 0
    total_radial_order_cases = 0
    total_patch_topologies = 0
    global_first_blocker_histogram: Counter[str] = Counter()

    for internal_count in internal_counts:
        patch_topology_count = 0
        radial_order_case_count = 0
        profile_preserving_case_count = 0
        normal_form_prefix_passing_case_count = 0
        first_blocker_histogram: Counter[str] = Counter()
        minimum_small_cut_histogram: Counter[str] = Counter()

        for patch_edges in iter_simple_patch_edge_sets(internal_count):
            patch_topology_count += 1
            model0, _patch_edge_names0, radial_edges0 = simple_patch_model(
                base_model,
                patch_edges,
            )
            radial_orders = (radial_edges0, tuple(reversed(radial_edges0)))
            for radial_order in radial_orders:
                radial_order_case_count += 1
                model, patch_edge_names, radial_edges = simple_patch_model(
                    base_model,
                    patch_edges,
                    radial_order,
                )
                state_extensions: list[dict[str, object]] = []
                for state_payload in base_states:
                    assert isinstance(state_payload, dict)
                    raw_state = state_payload.get("state", {})
                    desired_profile = state_payload.get("winding_profile", [])
                    assert isinstance(raw_state, dict)
                    assert isinstance(desired_profile, list)
                    fixed_edge_colors = {
                        edge: str(raw_state[edge])
                        for edge in base_model.gadget.edges
                        if edge not in PATCH_REMOVED_PARALLEL_EDGES
                    }
                    extension = simple_patch_profile_preserving_extension(
                        model,
                        patch_edge_names,
                        radial_edges,
                        fixed_edge_colors,
                        desired_profile,
                    )
                    if extension is None:
                        break
                    state_extensions.append(
                        {
                            "state_index": state_payload.get("state_index"),
                            "profile_preserved": True,
                        }
                    )
                else:
                    profile_preserving_case_count += 1
                    total_profile_preserving_cases += 1
                    graph_audit = closed_collar_multigraph_audit(model)
                    first_blocker = graph_audit["first_failed_normal_form_test"]
                    first_blocker_name = (
                        first_blocker["name"] if first_blocker else "none"
                    )
                    first_blocker_histogram[first_blocker_name] += 1
                    global_first_blocker_histogram[first_blocker_name] += 1
                    small_cuts = graph_audit["small_cyclic_cuts"]
                    minimum_small_cut = (
                        min(int(cut["cut_size"]) for cut in small_cuts)
                        if small_cuts
                        else None
                    )
                    minimum_small_cut_histogram[
                        str(minimum_small_cut) if minimum_small_cut is not None else "none"
                    ] += 1
                    if first_blocker is None:
                        normal_form_prefix_passing_case_count += 1
                        total_normal_form_prefix_passing_cases += 1
                    should_sample = (
                        len(profile_preserving_samples) < sample_limit
                        or first_blocker_name not in sampled_first_blockers
                    )
                    if should_sample:
                        sampled_first_blockers.add(first_blocker_name)
                        profile_preserving_samples.append(
                            {
                                "internal_vertex_count": internal_count,
                                "patch_edges": [
                                    list(edge_pair) for edge_pair in patch_edges
                                ],
                                "radial_order": list(radial_edges),
                                "state_extensions": state_extensions,
                                "graph_summary": {
                                    "vertex_count": graph_audit["vertex_count"],
                                    "edge_count": graph_audit["edge_count"],
                                    "first_failed_normal_form_test": (
                                        first_blocker_name
                                        if first_blocker_name != "none"
                                        else None
                                    ),
                                    "passed_normal_form_tests": [
                                        test["name"]
                                        for test in graph_audit["normal_form_tests"]
                                        if bool(test["passes"])
                                    ],
                                    "blocked_normal_form_tests": [
                                        test["name"]
                                        for test in graph_audit["normal_form_tests"]
                                        if not bool(test["passes"])
                                    ],
                                    "small_cyclic_cut_count": len(small_cuts),
                                    "minimum_small_cyclic_cut_size": minimum_small_cut,
                                    "small_cyclic_cut_samples": small_cuts[:5],
                                },
                            }
                        )

        total_radial_order_cases += radial_order_case_count
        total_patch_topologies += patch_topology_count
        reports.append(
            {
                "internal_vertex_count": internal_count,
                "patch_topology_count": patch_topology_count,
                "radial_order_case_count": radial_order_case_count,
                "profile_preserving_case_count": profile_preserving_case_count,
                "normal_form_prefix_passing_profile_case_count":
                    normal_form_prefix_passing_case_count,
                "first_failed_normal_form_histogram":
                    dict(sorted(first_blocker_histogram.items())),
                "minimum_small_cyclic_cut_size_histogram":
                    dict(sorted(minimum_small_cut_histogram.items())),
            }
        )

    if total_normal_form_prefix_passing_cases:
        verdict = "bounded_simple_patch_search_found_normal_form_prefix_realization"
    elif not total_profile_preserving_cases:
        verdict = "bounded_simple_patch_search_found_no_profile_preserving_patch"
    else:
        blocker_names = set(global_first_blocker_histogram)
        if blocker_names == {"no_cyclic_edge_cut_of_size_at_most_four"}:
            verdict = (
                "bounded_simple_patch_search_blocked_by_"
                "no_cyclic_edge_cut_of_size_at_most_four"
            )
        elif blocker_names <= {
            "planar_multigraph",
            "no_cyclic_edge_cut_of_size_at_most_four",
        }:
            verdict = (
                "bounded_simple_patch_search_blocked_by_"
                "planarity_or_no_cyclic_edge_cut_of_size_at_most_four"
            )
        else:
            verdict = "bounded_simple_patch_search_blocked_by_mixed_normal_form_prefix"
    return {
        "schema": "fourcolor-section-9-2-closed-collar-winding-simple-patch-search-v1",
        "source": "Section 9.2 bounded simple cubic patch search for the closed-collar winding-freedom witness",
        "run_id": f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}::simple_patch_le_{max_internal_vertices}",
        "word": list(word_names(word)),
        "fixed_outer_key": list(fixed_outer_key),
        "search": {
            "max_internal_vertices": max_internal_vertices,
            "internal_vertex_counts": internal_counts,
            "patch_terminals": dict(PATCH_TERMINAL_VERTICES),
            "removed_parallel_edges": sorted(PATCH_REMOVED_PARALLEL_EDGES),
            "radial_cut_rule": (
                "C0 and C3 remain fixed; the two patch edges incident to terminal A "
                "replace C1/C2 and are tested in both orders with colors r,b"
            ),
            "profile_requirement": (
                "every state in the tau,tau::rrbb winding-freedom fiber must extend "
                "to a proper Tait coloring with exactly the same winding profile"
            ),
        },
        "base_winding_profile_histogram": base_fiber["winding_profile_histogram"],
        "per_internal_vertex_count": reports,
        "profile_preserving_samples": profile_preserving_samples,
        "summary": {
            "verdict": verdict,
            "patch_topology_count": total_patch_topologies,
            "radial_order_case_count": total_radial_order_cases,
            "profile_preserving_case_count": total_profile_preserving_cases,
            "normal_form_prefix_passing_profile_case_count":
                total_normal_form_prefix_passing_cases,
            "first_failed_normal_form_histogram":
                dict(sorted(global_first_blocker_histogram.items())),
        },
    }


def audit_closed_collar_winding_simple_patch_slice(
    tau_states: list[tuple[str, ...]],
    internal_vertex_count: int,
    patch_start_index: int,
    patch_topology_limit: int,
    sample_limit: int,
) -> dict[str, object]:
    word = (TAU_TYPE, TAU_TYPE)
    fixed_outer_key = ("r", "r", "b", "b")
    base_model = build_closed_collar_model(word)
    base_fiber = audit_closed_collar_winding_fiber(
        word,
        fixed_outer_key,
        tau_states,
        include_all_components=True,
    )
    base_states = base_fiber.get("states", [])
    assert isinstance(base_states, list)
    if internal_vertex_count < 0 or internal_vertex_count % 2:
        raise ValueError("patch internal vertex count must be a nonnegative even number")
    if patch_start_index < 0:
        raise ValueError("patch start index must be nonnegative")
    if patch_topology_limit <= 0:
        raise ValueError("patch topology limit must be positive")

    processed_patch_topology_count = 0
    radial_order_case_count = 0
    profile_preserving_case_count = 0
    normal_form_prefix_passing_case_count = 0
    first_blocker_histogram: Counter[str] = Counter()
    minimum_small_cut_histogram: Counter[str] = Counter()
    profile_preserving_samples: list[dict[str, object]] = []
    sampled_first_blockers: set[str] = set()
    last_seen_patch_index: int | None = None
    exhausted = True

    for patch_index, patch_edges in enumerate(
        iter_simple_patch_edge_sets(internal_vertex_count)
    ):
        if patch_index < patch_start_index:
            continue
        if processed_patch_topology_count >= patch_topology_limit:
            exhausted = False
            break
        last_seen_patch_index = patch_index
        processed_patch_topology_count += 1

        model0, _patch_edge_names0, radial_edges0 = simple_patch_model(
            base_model,
            patch_edges,
        )
        radial_orders = (radial_edges0, tuple(reversed(radial_edges0)))
        for radial_order in radial_orders:
            radial_order_case_count += 1
            model, patch_edge_names, radial_edges = simple_patch_model(
                base_model,
                patch_edges,
                radial_order,
            )
            state_extensions: list[dict[str, object]] = []
            for state_payload in base_states:
                assert isinstance(state_payload, dict)
                raw_state = state_payload.get("state", {})
                desired_profile = state_payload.get("winding_profile", [])
                assert isinstance(raw_state, dict)
                assert isinstance(desired_profile, list)
                fixed_edge_colors = {
                    edge: str(raw_state[edge])
                    for edge in base_model.gadget.edges
                    if edge not in PATCH_REMOVED_PARALLEL_EDGES
                }
                extension = simple_patch_profile_preserving_extension(
                    model,
                    patch_edge_names,
                    radial_edges,
                    fixed_edge_colors,
                    desired_profile,
                )
                if extension is None:
                    break
                state_extensions.append(
                    {
                        "state_index": state_payload.get("state_index"),
                        "profile_preserved": True,
                    }
                )
            else:
                profile_preserving_case_count += 1
                graph_audit = closed_collar_multigraph_prefix_audit(
                    model,
                    sample_limit=sample_limit,
                )
                first_blocker = graph_audit["first_failed_normal_form_test"]
                first_blocker_name = first_blocker["name"] if first_blocker else "none"
                first_blocker_histogram[first_blocker_name] += 1
                small_cuts = graph_audit["small_cyclic_cuts"]
                minimum_small_cut = graph_audit["minimum_small_cyclic_cut_size"]
                minimum_small_cut_histogram[
                    str(minimum_small_cut)
                    if minimum_small_cut is not None
                    else "not_checked"
                    if not bool(graph_audit["small_cyclic_cuts_checked"])
                    else "none"
                ] += 1
                if first_blocker is None:
                    normal_form_prefix_passing_case_count += 1
                should_sample = (
                    len(profile_preserving_samples) < sample_limit
                    or first_blocker_name not in sampled_first_blockers
                )
                if should_sample:
                    sampled_first_blockers.add(first_blocker_name)
                    profile_preserving_samples.append(
                        {
                            "patch_index": patch_index,
                            "patch_edges": [
                                list(edge_pair) for edge_pair in patch_edges
                            ],
                            "radial_order": list(radial_edges),
                            "state_extensions": state_extensions,
                            "graph_summary": {
                                "vertex_count": graph_audit["vertex_count"],
                                "edge_count": graph_audit["edge_count"],
                                "first_failed_normal_form_test": (
                                    first_blocker_name
                                    if first_blocker_name != "none"
                                    else None
                                ),
                                "passed_normal_form_tests": [
                                    test["name"]
                                    for test in graph_audit["normal_form_tests"]
                                    if bool(test["passes"])
                                ],
                                "blocked_normal_form_tests": [
                                    test["name"]
                                    for test in graph_audit["normal_form_tests"]
                                    if not bool(test["passes"])
                                ],
                                "small_cyclic_cuts_checked":
                                    graph_audit["small_cyclic_cuts_checked"],
                                "small_cyclic_cut_sample_count":
                                    graph_audit["small_cyclic_cut_sample_count"],
                                "minimum_small_cyclic_cut_size": minimum_small_cut,
                                "small_cyclic_cut_samples": small_cuts[:5],
                            },
                        }
                    )

    next_patch_start_index = patch_start_index + processed_patch_topology_count
    if exhausted and last_seen_patch_index is not None:
        next_patch_start_index = last_seen_patch_index + 1
    verdict = (
        "simple_patch_slice_found_normal_form_prefix_realization"
        if normal_form_prefix_passing_case_count
        else "simple_patch_slice_found_profile_preserving_cases"
        if profile_preserving_case_count
        else "simple_patch_slice_found_no_profile_preserving_patch"
    )
    return {
        "schema": "fourcolor-section-9-2-closed-collar-winding-simple-patch-slice-v1",
        "source": "Section 9.2 sliced simple cubic patch search for the closed-collar winding-freedom witness",
        "run_id": (
            f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}::"
            f"simple_patch_{internal_vertex_count}_from_{patch_start_index}_"
            f"limit_{patch_topology_limit}"
        ),
        "word": list(word_names(word)),
        "fixed_outer_key": list(fixed_outer_key),
        "search": {
            "internal_vertex_count": internal_vertex_count,
            "patch_start_index": patch_start_index,
            "patch_topology_limit": patch_topology_limit,
            "next_patch_start_index": next_patch_start_index,
            "slice_exhausted_exact_size_space": exhausted,
            "patch_terminals": dict(PATCH_TERMINAL_VERTICES),
            "removed_parallel_edges": sorted(PATCH_REMOVED_PARALLEL_EDGES),
            "radial_cut_rule": (
                "C0 and C3 remain fixed; the two patch edges incident to terminal A "
                "replace C1/C2 and are tested in both orders with colors r,b"
            ),
            "profile_requirement": (
                "every state in the tau,tau::rrbb winding-freedom fiber must extend "
                "to a proper Tait coloring with exactly the same winding profile"
            ),
        },
        "base_winding_profile_histogram": base_fiber["winding_profile_histogram"],
        "profile_preserving_samples": profile_preserving_samples,
        "summary": {
            "verdict": verdict,
            "processed_patch_topology_count": processed_patch_topology_count,
            "radial_order_case_count": radial_order_case_count,
            "profile_preserving_case_count": profile_preserving_case_count,
            "normal_form_prefix_passing_profile_case_count":
                normal_form_prefix_passing_case_count,
            "first_failed_normal_form_histogram":
                dict(sorted(first_blocker_histogram.items())),
            "minimum_small_cyclic_cut_size_histogram":
                dict(sorted(minimum_small_cut_histogram.items())),
        },
    }


def audit_closed_collar_winding_simple_patch_cyclic_cut_shapes(
    tau_states: list[tuple[str, ...]],
    internal_vertex_count: int,
    patch_start_index: int,
    patch_topology_limit: int,
    sample_limit: int,
) -> dict[str, object]:
    word = (TAU_TYPE, TAU_TYPE)
    fixed_outer_key = ("r", "r", "b", "b")
    base_model = build_closed_collar_model(word)
    base_fiber = audit_closed_collar_winding_fiber(
        word,
        fixed_outer_key,
        tau_states,
        include_all_components=True,
    )
    base_states = base_fiber.get("states", [])
    assert isinstance(base_states, list)
    if internal_vertex_count < 0 or internal_vertex_count % 2:
        raise ValueError("patch internal vertex count must be a nonnegative even number")
    if patch_start_index < 0:
        raise ValueError("patch start index must be nonnegative")
    if patch_topology_limit <= 0:
        raise ValueError("patch topology limit must be positive")

    processed_patch_topology_count = 0
    radial_order_case_count = 0
    profile_preserving_case_count = 0
    cyclic_cut_blocker_case_count = 0
    first_blocker_histogram: Counter[str] = Counter()
    minimum_small_cut_histogram: Counter[str] = Counter()
    first_cut_shape_histogram: Counter[str] = Counter()
    first_cut_edge_kind_histogram: Counter[str] = Counter()
    first_cut_side_kind_histogram: Counter[str] = Counter()
    first_cut_edge_tuple_histogram: Counter[str] = Counter()
    first_cut_side_collar_vertices_histogram: Counter[str] = Counter()
    first_cut_template_histogram: Counter[str] = Counter()
    shape_samples: list[dict[str, object]] = []
    last_seen_patch_index: int | None = None
    exhausted = True

    for patch_index, patch_edges in enumerate(
        iter_simple_patch_edge_sets(internal_vertex_count)
    ):
        if patch_index < patch_start_index:
            continue
        if processed_patch_topology_count >= patch_topology_limit:
            exhausted = False
            break
        last_seen_patch_index = patch_index
        processed_patch_topology_count += 1

        model0, _patch_edge_names0, radial_edges0 = simple_patch_model(
            base_model,
            patch_edges,
        )
        radial_orders = (radial_edges0, tuple(reversed(radial_edges0)))
        for radial_order in radial_orders:
            radial_order_case_count += 1
            model, patch_edge_names, radial_edges = simple_patch_model(
                base_model,
                patch_edges,
                radial_order,
            )
            state_extensions: list[dict[str, object]] = []
            for state_payload in base_states:
                assert isinstance(state_payload, dict)
                raw_state = state_payload.get("state", {})
                desired_profile = state_payload.get("winding_profile", [])
                assert isinstance(raw_state, dict)
                assert isinstance(desired_profile, list)
                fixed_edge_colors = {
                    edge: str(raw_state[edge])
                    for edge in base_model.gadget.edges
                    if edge not in PATCH_REMOVED_PARALLEL_EDGES
                }
                extension = simple_patch_profile_preserving_extension(
                    model,
                    patch_edge_names,
                    radial_edges,
                    fixed_edge_colors,
                    desired_profile,
                )
                if extension is None:
                    break
                state_extensions.append(
                    {
                        "state_index": state_payload.get("state_index"),
                        "profile_preserved": True,
                    }
                )
            else:
                profile_preserving_case_count += 1
                graph_audit = closed_collar_multigraph_prefix_audit(
                    model,
                    sample_limit=sample_limit,
                )
                first_blocker = graph_audit["first_failed_normal_form_test"]
                first_blocker_name = first_blocker["name"] if first_blocker else "none"
                first_blocker_histogram[first_blocker_name] += 1
                if first_blocker_name != "no_cyclic_edge_cut_of_size_at_most_four":
                    continue

                cyclic_cut_blocker_case_count += 1
                small_cuts = graph_audit["small_cyclic_cuts"]
                minimum_small_cut = graph_audit["minimum_small_cyclic_cut_size"]
                minimum_small_cut_histogram[
                    str(minimum_small_cut)
                    if minimum_small_cut is not None
                    else "none"
                ] += 1
                if not small_cuts:
                    continue
                first_cut = small_cuts[0]
                shape = closed_collar_cut_shape_payload(first_cut)
                shape_key = closed_collar_cut_shape_key(first_cut)
                cut_edges_key = ",".join(sorted(str(edge) for edge in shape["cut_edges"]))
                side_collar_vertices = sorted(
                    str(vertex)
                    for vertex in shape["side_vertices"]
                    if closed_collar_vertex_kind(str(vertex)) == "collar"
                )
                side_collar_key = ",".join(side_collar_vertices)
                template_key = f"edges:{cut_edges_key}|sideCollar:{side_collar_key}"
                first_cut_shape_histogram[shape_key] += 1
                first_cut_edge_tuple_histogram[cut_edges_key] += 1
                first_cut_side_collar_vertices_histogram[side_collar_key] += 1
                first_cut_template_histogram[template_key] += 1
                for key, count in shape["edge_kind_histogram"].items():
                    first_cut_edge_kind_histogram[f"{key}:{count}"] += 1
                for key, count in shape["side_vertex_kind_histogram"].items():
                    first_cut_side_kind_histogram[f"{key}:{count}"] += 1
                if len(shape_samples) < sample_limit:
                    shape_samples.append(
                        {
                            "patch_index": patch_index,
                            "radial_order": list(radial_edges),
                            "state_extensions": state_extensions,
                            "first_cut_shape_key": shape_key,
                            "first_cut_shape": shape,
                            "first_cut_template_key": template_key,
                            "minimum_small_cyclic_cut_size": minimum_small_cut,
                            "small_cyclic_cut_sample_count":
                                graph_audit["small_cyclic_cut_sample_count"],
                            "patch_edges": [
                                list(edge_pair) for edge_pair in patch_edges
                            ],
                        }
                    )

    next_patch_start_index = patch_start_index + processed_patch_topology_count
    if exhausted and last_seen_patch_index is not None:
        next_patch_start_index = last_seen_patch_index + 1
    return {
        "schema": "fourcolor-section-9-2-closed-collar-winding-simple-patch-cyclic-cut-shapes-v1",
        "source": (
            "Cyclic-cut shape audit for profile-preserving simple patches in "
            "the closed-collar winding-freedom realization lab"
        ),
        "run_id": (
            f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}::"
            f"simple_patch_{internal_vertex_count}_cyclic_cut_shapes_from_"
            f"{patch_start_index}_limit_{patch_topology_limit}"
        ),
        "word": list(word_names(word)),
        "fixed_outer_key": list(fixed_outer_key),
        "search": {
            "internal_vertex_count": internal_vertex_count,
            "patch_start_index": patch_start_index,
            "patch_topology_limit": patch_topology_limit,
            "next_patch_start_index": next_patch_start_index,
            "slice_exhausted_exact_size_space": exhausted,
            "patch_terminals": dict(PATCH_TERMINAL_VERTICES),
            "removed_parallel_edges": sorted(PATCH_REMOVED_PARALLEL_EDGES),
            "classification": (
                "for each profile-preserving case whose first blocker is "
                "no_cyclic_edge_cut_of_size_at_most_four, classify the first "
                "sampled cyclic cut by cut size, side size, edge kinds, and "
                "side vertex kinds"
            ),
        },
        "base_winding_profile_histogram": base_fiber["winding_profile_histogram"],
        "shape_samples": shape_samples,
        "summary": {
            "processed_patch_topology_count": processed_patch_topology_count,
            "radial_order_case_count": radial_order_case_count,
            "profile_preserving_case_count": profile_preserving_case_count,
            "cyclic_cut_blocker_case_count": cyclic_cut_blocker_case_count,
            "first_failed_normal_form_histogram":
                dict(sorted(first_blocker_histogram.items())),
            "minimum_small_cyclic_cut_size_histogram":
                dict(sorted(minimum_small_cut_histogram.items())),
            "first_cut_shape_histogram":
                dict(sorted(first_cut_shape_histogram.items())),
            "first_cut_edge_kind_histogram":
                dict(sorted(first_cut_edge_kind_histogram.items())),
            "first_cut_side_vertex_kind_histogram":
                dict(sorted(first_cut_side_kind_histogram.items())),
            "first_cut_edge_tuple_histogram":
                dict(sorted(first_cut_edge_tuple_histogram.items())),
            "first_cut_side_collar_vertices_histogram":
                dict(sorted(first_cut_side_collar_vertices_histogram.items())),
            "first_cut_template_histogram":
                dict(sorted(first_cut_template_histogram.items())),
        },
    }


STRUCTURAL_TEMPLATE_BLOCKERS = frozenset(
    (
        "connected_multigraph",
        "cubic_multigraph",
        "bridgeless_multigraph",
        "planar_multigraph",
        "simple_endpoint_realization",
    )
)


def classify_simple_patch_template_blocker_case(
    base_model: CompositeModel,
    base_states: list[object],
    patch_index: int,
    patch_edges: tuple[tuple[str, str], ...],
    radial_order: tuple[str, str],
    sample_limit: int,
) -> dict[str, object] | None:
    model, patch_edge_names, radial_edges = simple_patch_model(
        base_model,
        patch_edges,
        radial_order,
    )
    state_extensions: list[dict[str, object]] = []
    for state_payload in base_states:
        assert isinstance(state_payload, dict)
        raw_state = state_payload.get("state", {})
        desired_profile = state_payload.get("winding_profile", [])
        assert isinstance(raw_state, dict)
        assert isinstance(desired_profile, list)
        fixed_edge_colors = {
            edge: str(raw_state[edge])
            for edge in base_model.gadget.edges
            if edge not in PATCH_REMOVED_PARALLEL_EDGES
        }
        extension = simple_patch_profile_preserving_extension(
            model,
            patch_edge_names,
            radial_edges,
            fixed_edge_colors,
            desired_profile,
        )
        if extension is None:
            return None
        state_extensions.append(
            {
                "state_index": state_payload.get("state_index"),
                "profile_preserved": True,
            }
        )

    graph_audit = closed_collar_multigraph_prefix_audit(
        model,
        sample_limit=sample_limit,
    )
    first_blocker = graph_audit["first_failed_normal_form_test"]
    first_blocker_name = first_blocker["name"] if first_blocker else "none"
    if first_blocker_name in STRUCTURAL_TEMPLATE_BLOCKERS:
        return {
            "blocker_name": first_blocker_name,
            "patch_index": patch_index,
            "patch_edges": patch_edges,
            "radial_edges": radial_edges,
            "state_extensions": state_extensions,
            "payload": {
                "graph_summary": {
                    "vertex_count": graph_audit["vertex_count"],
                    "edge_count": graph_audit["edge_count"],
                    "first_failed_normal_form_test": first_blocker_name,
                }
            },
        }

    vertices, edges = multigraph_vertices_and_edges(model)
    template_cut = first_matching_cyclic_cut_payload(
        vertices,
        edges,
        4,
        closed_collar_cut_is_exact_diagonal_template,
    )
    if template_cut is not None:
        template_key = closed_collar_cut_template_key(template_cut)
        return {
            "blocker_name": "excluded_exact_diagonal_two_pole_template",
            "patch_index": patch_index,
            "patch_edges": patch_edges,
            "radial_edges": radial_edges,
            "state_extensions": state_extensions,
            "exact_template_key": template_key,
            "payload": {
                "exact_template_key": template_key,
                "exact_template_cut": closed_collar_cut_shape_payload(template_cut),
            },
        }

    small_cuts = cyclic_cut_payloads(vertices, edges, 4)
    if small_cuts:
        minimum_small_cut = min(int(cut["cut_size"]) for cut in small_cuts)
        return {
            "blocker_name": "non_template_cyclic_edge_cut_of_size_at_most_four",
            "patch_index": patch_index,
            "patch_edges": patch_edges,
            "radial_edges": radial_edges,
            "state_extensions": state_extensions,
            "minimum_small_cut": minimum_small_cut,
            "payload": {
                "minimum_small_cyclic_cut_size": minimum_small_cut,
                "small_cyclic_cut_count": len(small_cuts),
                "first_small_cyclic_cut":
                    closed_collar_cut_shape_payload(small_cuts[0]),
            },
        }

    cap5_like = cap5_like_payloads(vertices, edges)
    if cap5_like:
        return {
            "blocker_name": "cap5_free_literal_five_cycle_test",
            "patch_index": patch_index,
            "patch_edges": patch_edges,
            "radial_edges": radial_edges,
            "state_extensions": state_extensions,
            "payload": {
                "cap5_like_cut_count": len(cap5_like),
                "cap5_like_cut_sample": cap5_like[:sample_limit],
            },
        }

    return {
        "blocker_name": "none_after_template_exclusion",
        "patch_index": patch_index,
        "patch_edges": patch_edges,
        "radial_edges": radial_edges,
        "state_extensions": state_extensions,
        "payload": {
            "graph_summary": {
                "vertex_count": graph_audit["vertex_count"],
                "edge_count": graph_audit["edge_count"],
            }
        },
    }


def add_template_blocker_sample(
    samples: list[dict[str, object]],
    sampled_blockers: set[str],
    sample_limit: int,
    case_result: dict[str, object],
) -> None:
    blocker_name = str(case_result["blocker_name"])
    if len(samples) >= sample_limit and blocker_name in sampled_blockers:
        return
    sampled_blockers.add(blocker_name)
    patch_edges = case_result["patch_edges"]
    radial_edges = case_result["radial_edges"]
    payload = case_result["payload"]
    assert isinstance(patch_edges, tuple)
    assert isinstance(radial_edges, tuple)
    assert isinstance(payload, dict)
    samples.append(
        {
            "patch_index": case_result["patch_index"],
            "patch_edges": [list(edge_pair) for edge_pair in patch_edges],
            "radial_order": list(radial_edges),
            "state_extensions": case_result["state_extensions"],
            "template_exclusion_blocker": blocker_name,
            **payload,
        }
    )


def planar_rotation_system_radial_face_audit(
    model: CompositeModel,
    max_rotation_systems: int,
    sample_limit: int,
) -> dict[str, object]:
    vertices, edges = multigraph_vertices_and_edges(model)
    edge_by_pair: dict[tuple[str, str], str] = {}
    adjacency: dict[str, list[str]] = {vertex: [] for vertex in vertices}
    for edge, u, v in edges:
        if u == v:
            return {
                "checked": False,
                "failure": "loop_edge",
                "loop_edge": edge,
            }
        key = tuple(sorted((u, v)))
        if key in edge_by_pair:
            return {
                "checked": False,
                "failure": "parallel_edge_pair",
                "parallel_edges": [edge_by_pair[key], edge],
                "endpoints": list(key),
            }
        edge_by_pair[key] = edge
        adjacency[u].append(v)
        adjacency[v].append(u)

    vertex_order = tuple(sorted(vertices))
    neighbor_order = {
        vertex: tuple(sorted(adjacency[vertex])) for vertex in vertex_order
    }
    high_degree_vertices = [
        vertex for vertex in vertex_order if len(neighbor_order[vertex]) > 3
    ]
    if high_degree_vertices:
        return {
            "checked": False,
            "failure": "degree_above_three_unsupported_by_cubic_rotation_audit",
            "high_degree_vertices": high_degree_vertices,
        }
    orientation_vertices = tuple(
        vertex for vertex in vertex_order if len(neighbor_order[vertex]) > 2
    )
    total_rotation_system_count = 2 ** len(orientation_vertices)
    radial_cut_edges = tuple(model.closing_edges)
    radial_cut_set = set(radial_cut_edges)
    enumerated_rotation_system_count = 0
    planar_rotation_system_count = 0
    radial_face_coherent_rotation_count = 0
    max_radial_edges_on_face_histogram: Counter[str] = Counter()
    planar_samples: list[dict[str, object]] = []
    coherent_samples: list[dict[str, object]] = []
    orientation_index = {vertex: i for i, vertex in enumerate(orientation_vertices)}

    def rotation_for_mask(mask: int) -> dict[str, tuple[str, ...]]:
        rotation: dict[str, tuple[str, ...]] = {}
        for vertex in vertex_order:
            order = neighbor_order[vertex]
            bit_index = orientation_index.get(vertex)
            if bit_index is not None and ((mask >> bit_index) & 1):
                order = tuple(reversed(order))
            rotation[vertex] = order
        return rotation

    def faces_for_rotation(
        rotation: dict[str, tuple[str, ...]],
    ) -> list[dict[str, object]]:
        seen: set[tuple[str, str]] = set()
        faces: list[dict[str, object]] = []
        for u in vertex_order:
            for v in rotation[u]:
                start = (u, v)
                if start in seen:
                    continue
                face_vertices: list[str] = []
                face_edges: list[str] = []
                current = start
                while current not in seen:
                    seen.add(current)
                    a, b = current
                    face_vertices.append(a)
                    face_edges.append(edge_by_pair[tuple(sorted((a, b)))])
                    order_at_b = rotation[b]
                    i = order_at_b.index(a)
                    next_vertex = order_at_b[(i - 1) % len(order_at_b)]
                    current = (b, next_vertex)
                radial_edges = [edge for edge in face_edges if edge in radial_cut_set]
                faces.append(
                    {
                        "vertices": face_vertices,
                        "edges": face_edges,
                        "radial_cut_edges": radial_edges,
                        "radial_cut_edge_count": len(radial_edges),
                    }
                )
        return faces

    def radial_face_sample(
        rotation_mask: int,
        faces: list[dict[str, object]],
        max_radial_edges_on_face: int,
    ) -> dict[str, object]:
        radial_faces = [
            face for face in faces if int(face["radial_cut_edge_count"]) > 0
        ]
        radial_faces.sort(
            key=lambda face: (
                -int(face["radial_cut_edge_count"]),
                len(face["vertices"]),
                face["vertices"],
            )
        )
        return {
            "rotation_mask": rotation_mask,
            "face_count": len(faces),
            "max_radial_cut_edges_on_single_face": max_radial_edges_on_face,
            "radial_cut_faces": radial_faces[:sample_limit],
        }

    for mask in range(total_rotation_system_count):
        if enumerated_rotation_system_count >= max_rotation_systems:
            break
        enumerated_rotation_system_count += 1
        rotation = rotation_for_mask(mask)
        faces = faces_for_rotation(rotation)
        if len(vertices) - len(edges) + len(faces) != 2:
            continue
        planar_rotation_system_count += 1
        max_radial_edges_on_face = max(
            int(face["radial_cut_edge_count"]) for face in faces
        )
        max_radial_edges_on_face_histogram[str(max_radial_edges_on_face)] += 1
        sample = radial_face_sample(mask, faces, max_radial_edges_on_face)
        if len(planar_samples) < sample_limit:
            planar_samples.append(sample)
        if max_radial_edges_on_face == len(radial_cut_edges):
            radial_face_coherent_rotation_count += 1
            if len(coherent_samples) < sample_limit:
                coherent_samples.append(sample)

    return {
        "checked": True,
        "vertex_count": len(vertices),
        "edge_count": len(edges),
        "radial_cut_edges": list(radial_cut_edges),
        "orientation_vertex_count": len(orientation_vertices),
        "total_rotation_system_count": total_rotation_system_count,
        "enumerated_rotation_system_count": enumerated_rotation_system_count,
        "rotation_system_enumeration_exhausted":
            enumerated_rotation_system_count == total_rotation_system_count,
        "planar_rotation_system_count": planar_rotation_system_count,
        "radial_face_coherent_rotation_count":
            radial_face_coherent_rotation_count,
        "max_radial_cut_edges_on_single_face_histogram":
            dict(sorted(max_radial_edges_on_face_histogram.items())),
        "planar_embedding_samples": planar_samples,
        "radial_face_coherent_samples": coherent_samples,
    }


def audit_closed_collar_winding_simple_patch_annular_embedding_sample(
    tau_states: list[tuple[str, ...]],
    internal_vertex_count: int,
    patch_indices: tuple[int, ...],
    radial_order_indices: tuple[int, ...],
    sample_limit: int,
    max_rotation_systems: int,
) -> dict[str, object]:
    word = (TAU_TYPE, TAU_TYPE)
    fixed_outer_key = ("r", "r", "b", "b")
    base_model = build_closed_collar_model(word)
    base_fiber = audit_closed_collar_winding_fiber(
        word,
        fixed_outer_key,
        tau_states,
        include_all_components=True,
    )
    base_states = base_fiber.get("states", [])
    assert isinstance(base_states, list)
    exact_patch_topology_count = simple_patch_edge_set_count(internal_vertex_count)
    if not patch_indices:
        raise ValueError("patch index sample must be nonempty")
    if not radial_order_indices:
        raise ValueError("radial order index sample must be nonempty")
    if max_rotation_systems <= 0:
        raise ValueError("maximum rotation systems must be positive")
    for patch_index in patch_indices:
        if patch_index < 0 or patch_index >= exact_patch_topology_count:
            raise ValueError(
                f"patch index {patch_index} is outside "
                f"[0, {exact_patch_topology_count})"
            )
    for radial_order_index in radial_order_indices:
        if radial_order_index not in (0, 1):
            raise ValueError("radial order indices must be 0 or 1")

    sampled_patch_topology_count = len(patch_indices)
    radial_order_case_count = 0
    profile_preserving_case_count = 0
    planar_profile_preserving_case_count = 0
    radial_face_coherent_case_count = 0
    radial_face_incoherent_case_count = 0
    total_rotation_system_count = 0
    enumerated_rotation_system_count = 0
    planar_rotation_system_count = 0
    radial_face_coherent_rotation_count = 0
    blocker_histogram: Counter[str] = Counter()
    exact_template_histogram: Counter[str] = Counter()
    max_radial_edges_histogram: Counter[str] = Counter()
    samples: list[dict[str, object]] = []

    for patch_index in patch_indices:
        patch_edges = simple_patch_edge_set_at_index(
            internal_vertex_count,
            patch_index,
        )
        model0, _patch_edge_names0, radial_edges0 = simple_patch_model(
            base_model,
            patch_edges,
        )
        radial_orders = (radial_edges0, tuple(reversed(radial_edges0)))
        for radial_order_index in radial_order_indices:
            radial_order = radial_orders[radial_order_index]
            radial_order_case_count += 1
            case_result = classify_simple_patch_template_blocker_case(
                base_model,
                base_states,
                patch_index,
                patch_edges,
                radial_order,
                sample_limit,
            )
            if case_result is None:
                continue
            profile_preserving_case_count += 1
            blocker_name = str(case_result["blocker_name"])
            blocker_histogram[blocker_name] += 1
            exact_template_key = case_result.get("exact_template_key")
            if exact_template_key is not None:
                exact_template_histogram[str(exact_template_key)] += 1
            if blocker_name in STRUCTURAL_TEMPLATE_BLOCKERS:
                payload = case_result["payload"]
                assert isinstance(payload, dict)
                if len(samples) < sample_limit:
                    samples.append(
                        {
                            "patch_index": patch_index,
                            "radial_order_index": radial_order_index,
                            "radial_order": list(radial_order),
                            "template_exclusion_blocker": blocker_name,
                            "embedding_audit_skipped": "structural_blocker",
                            **payload,
                        }
                    )
                continue

            planar_profile_preserving_case_count += 1
            model, _patch_edge_names, radial_edges = simple_patch_model(
                base_model,
                patch_edges,
                radial_order,
            )
            embedding_audit = planar_rotation_system_radial_face_audit(
                model,
                max_rotation_systems=max_rotation_systems,
                sample_limit=sample_limit,
            )
            if embedding_audit.get("checked") is True:
                total_rotation_system_count += int(
                    embedding_audit["total_rotation_system_count"]
                )
                enumerated_rotation_system_count += int(
                    embedding_audit["enumerated_rotation_system_count"]
                )
                planar_rotation_system_count += int(
                    embedding_audit["planar_rotation_system_count"]
                )
                coherent_rotation_count = int(
                    embedding_audit["radial_face_coherent_rotation_count"]
                )
                radial_face_coherent_rotation_count += coherent_rotation_count
                if coherent_rotation_count:
                    radial_face_coherent_case_count += 1
                else:
                    radial_face_incoherent_case_count += 1
                histogram = embedding_audit[
                    "max_radial_cut_edges_on_single_face_histogram"
                ]
                assert isinstance(histogram, dict)
                for key, count in histogram.items():
                    max_radial_edges_histogram[str(key)] += int(count)
            if len(samples) < sample_limit:
                payload = case_result["payload"]
                assert isinstance(payload, dict)
                samples.append(
                    {
                        "patch_index": patch_index,
                        "radial_order_index": radial_order_index,
                        "patch_edges": [list(edge_pair) for edge_pair in patch_edges],
                        "radial_order": list(radial_edges),
                        "template_exclusion_blocker": blocker_name,
                        **payload,
                        "embedding_audit": embedding_audit,
                    }
                )

    verdict = (
        "annular_embedding_sample_found_radial_face_coherent_candidate"
        if radial_face_coherent_case_count
        else "annular_embedding_sample_found_no_radial_face_coherence"
        if planar_profile_preserving_case_count
        else "annular_embedding_sample_found_no_planar_profile_preserving_case"
    )
    return {
        "schema": (
            "fourcolor-section-9-2-closed-collar-winding-simple-patch-"
            "annular-embedding-sample-v1"
        ),
        "source": (
            "Annular embedding constraint audit for profile-preserving simple "
            "patches in the closed-collar winding-freedom realization lab"
        ),
        "run_id": (
            f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}::"
            f"simple_patch_{internal_vertex_count}_annular_embedding_"
            f"indexed_{sampled_patch_topology_count}_radial_orders_"
            f"{'_'.join(str(i) for i in radial_order_indices)}"
        ),
        "word": list(word_names(word)),
        "fixed_outer_key": list(fixed_outer_key),
        "search": {
            "internal_vertex_count": internal_vertex_count,
            "exact_patch_topology_count": exact_patch_topology_count,
            "sampled_patch_indices": list(patch_indices),
            "sampled_patch_topology_count": sampled_patch_topology_count,
            "sampled_radial_order_indices": list(radial_order_indices),
            "max_rotation_systems_per_case": max_rotation_systems,
            "radial_face_coherence_condition": (
                "there exists a planar rotation system with all four radial "
                "cut edges on a single face of the cut-open collar graph"
            ),
            "patch_terminals": dict(PATCH_TERMINAL_VERTICES),
            "removed_parallel_edges": sorted(PATCH_REMOVED_PARALLEL_EDGES),
        },
        "base_winding_profile_histogram": base_fiber["winding_profile_histogram"],
        "samples": samples,
        "summary": {
            "verdict": verdict,
            "sampled_patch_topology_count": sampled_patch_topology_count,
            "radial_order_case_count": radial_order_case_count,
            "profile_preserving_case_count": profile_preserving_case_count,
            "planar_profile_preserving_case_count":
                planar_profile_preserving_case_count,
            "radial_face_coherent_case_count": radial_face_coherent_case_count,
            "radial_face_incoherent_case_count": radial_face_incoherent_case_count,
            "total_rotation_system_count": total_rotation_system_count,
            "enumerated_rotation_system_count": enumerated_rotation_system_count,
            "planar_rotation_system_count": planar_rotation_system_count,
            "radial_face_coherent_rotation_count":
                radial_face_coherent_rotation_count,
            "template_exclusion_blocker_histogram":
                dict(sorted(blocker_histogram.items())),
            "exact_template_histogram":
                dict(sorted(exact_template_histogram.items())),
            "max_radial_cut_edges_on_single_face_histogram":
                dict(sorted(max_radial_edges_histogram.items())),
        },
    }


def audit_closed_collar_winding_simple_patch_annular_embedding_slice(
    tau_states: list[tuple[str, ...]],
    internal_vertex_count: int,
    patch_start_index: int,
    patch_topology_limit: int,
    radial_order_indices: tuple[int, ...],
    sample_limit: int,
    max_rotation_systems: int,
    embedding_case_limit: int,
) -> dict[str, object]:
    word = (TAU_TYPE, TAU_TYPE)
    fixed_outer_key = ("r", "r", "b", "b")
    base_model = build_closed_collar_model(word)
    base_fiber = audit_closed_collar_winding_fiber(
        word,
        fixed_outer_key,
        tau_states,
        include_all_components=True,
    )
    base_states = base_fiber.get("states", [])
    assert isinstance(base_states, list)
    exact_patch_topology_count = simple_patch_edge_set_count(internal_vertex_count)
    if internal_vertex_count < 0 or internal_vertex_count % 2:
        raise ValueError("patch internal vertex count must be a nonnegative even number")
    if patch_start_index < 0:
        raise ValueError("patch start index must be nonnegative")
    if patch_start_index >= exact_patch_topology_count:
        raise ValueError(
            f"patch start index {patch_start_index} is outside "
            f"[0, {exact_patch_topology_count})"
        )
    if patch_topology_limit <= 0:
        raise ValueError("patch topology limit must be positive")
    if not radial_order_indices:
        raise ValueError("radial order index sample must be nonempty")
    if max_rotation_systems <= 0:
        raise ValueError("maximum rotation systems must be positive")
    if embedding_case_limit <= 0:
        raise ValueError("embedding case limit must be positive")
    for radial_order_index in radial_order_indices:
        if radial_order_index not in (0, 1):
            raise ValueError("radial order indices must be 0 or 1")

    processed_patch_topology_count = 0
    radial_order_case_count = 0
    profile_preserving_case_count = 0
    structural_skipped_case_count = 0
    embedding_audited_case_count = 0
    radial_face_coherent_case_count = 0
    radial_face_incoherent_case_count = 0
    total_rotation_system_count = 0
    enumerated_rotation_system_count = 0
    planar_rotation_system_count = 0
    radial_face_coherent_rotation_count = 0
    blocker_histogram: Counter[str] = Counter()
    exact_template_histogram: Counter[str] = Counter()
    max_radial_edges_histogram: Counter[str] = Counter()
    samples: list[dict[str, object]] = []
    last_seen_patch_index: int | None = None
    exhausted = True
    stopped_by_embedding_case_limit = False
    resume_patch_start_index: int | None = None
    resume_radial_order_indices: tuple[int, ...] = radial_order_indices

    for patch_index, patch_edges in enumerate(
        iter_simple_patch_edge_sets(internal_vertex_count)
    ):
        if patch_index < patch_start_index:
            continue
        if processed_patch_topology_count >= patch_topology_limit:
            exhausted = False
            break
        last_seen_patch_index = patch_index
        processed_patch_topology_count += 1

        model0, _patch_edge_names0, radial_edges0 = simple_patch_model(
            base_model,
            patch_edges,
        )
        radial_orders = (radial_edges0, tuple(reversed(radial_edges0)))
        for radial_order_position, radial_order_index in enumerate(radial_order_indices):
            radial_order = radial_orders[radial_order_index]
            radial_order_case_count += 1
            case_result = classify_simple_patch_template_blocker_case(
                base_model,
                base_states,
                patch_index,
                patch_edges,
                radial_order,
                sample_limit,
            )
            if case_result is None:
                continue
            profile_preserving_case_count += 1
            blocker_name = str(case_result["blocker_name"])
            blocker_histogram[blocker_name] += 1
            exact_template_key = case_result.get("exact_template_key")
            if exact_template_key is not None:
                exact_template_histogram[str(exact_template_key)] += 1
            if blocker_name in STRUCTURAL_TEMPLATE_BLOCKERS:
                structural_skipped_case_count += 1
                payload = case_result["payload"]
                assert isinstance(payload, dict)
                if len(samples) < sample_limit:
                    samples.append(
                        {
                            "patch_index": patch_index,
                            "radial_order_index": radial_order_index,
                            "radial_order": list(radial_order),
                            "template_exclusion_blocker": blocker_name,
                            "embedding_audit_skipped": "structural_blocker",
                            **payload,
                        }
                    )
                continue

            model, _patch_edge_names, radial_edges = simple_patch_model(
                base_model,
                patch_edges,
                radial_order,
            )
            embedding_audit = planar_rotation_system_radial_face_audit(
                model,
                max_rotation_systems=max_rotation_systems,
                sample_limit=sample_limit,
            )
            embedding_audited_case_count += 1
            if embedding_audit.get("checked") is True:
                total_rotation_system_count += int(
                    embedding_audit["total_rotation_system_count"]
                )
                enumerated_rotation_system_count += int(
                    embedding_audit["enumerated_rotation_system_count"]
                )
                planar_rotation_system_count += int(
                    embedding_audit["planar_rotation_system_count"]
                )
                coherent_rotation_count = int(
                    embedding_audit["radial_face_coherent_rotation_count"]
                )
                radial_face_coherent_rotation_count += coherent_rotation_count
                if coherent_rotation_count:
                    radial_face_coherent_case_count += 1
                else:
                    radial_face_incoherent_case_count += 1
                histogram = embedding_audit[
                    "max_radial_cut_edges_on_single_face_histogram"
                ]
                assert isinstance(histogram, dict)
                for key, count in histogram.items():
                    max_radial_edges_histogram[str(key)] += int(count)
            if len(samples) < sample_limit:
                payload = case_result["payload"]
                assert isinstance(payload, dict)
                samples.append(
                    {
                        "patch_index": patch_index,
                        "radial_order_index": radial_order_index,
                        "patch_edges": [list(edge_pair) for edge_pair in patch_edges],
                        "radial_order": list(radial_edges),
                        "template_exclusion_blocker": blocker_name,
                        **payload,
                        "embedding_audit": embedding_audit,
                    }
                )
            if embedding_audited_case_count >= embedding_case_limit:
                stopped_by_embedding_case_limit = True
                remaining_radial_orders = radial_order_indices[
                    radial_order_position + 1:
                ]
                if remaining_radial_orders:
                    resume_patch_start_index = patch_index
                    resume_radial_order_indices = remaining_radial_orders
                else:
                    resume_patch_start_index = patch_index + 1
                    resume_radial_order_indices = radial_order_indices
                break
        if stopped_by_embedding_case_limit:
            exhausted = False
            break

    if resume_patch_start_index is None:
        next_patch_start_index = patch_start_index + processed_patch_topology_count
        if exhausted and last_seen_patch_index is not None:
            next_patch_start_index = last_seen_patch_index + 1
        resume_patch_start_index = next_patch_start_index

    verdict = (
        "annular_embedding_slice_found_radial_face_coherent_candidate"
        if radial_face_coherent_case_count
        else "annular_embedding_slice_found_no_radial_face_coherence"
        if embedding_audited_case_count
        else "annular_embedding_slice_found_no_embedding_audited_case"
        if profile_preserving_case_count
        else "annular_embedding_slice_found_no_profile_preserving_patch"
    )
    return {
        "schema": (
            "fourcolor-section-9-2-closed-collar-winding-simple-patch-"
            "annular-embedding-slice-v1"
        ),
        "source": (
            "Sliced annular embedding constraint audit for profile-preserving "
            "simple patches in the closed-collar winding-freedom realization lab"
        ),
        "run_id": (
            f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}::"
            f"simple_patch_{internal_vertex_count}_annular_embedding_from_"
            f"{patch_start_index}_limit_{patch_topology_limit}_cases_"
            f"{embedding_case_limit}_radial_orders_"
            f"{'_'.join(str(i) for i in radial_order_indices)}"
        ),
        "word": list(word_names(word)),
        "fixed_outer_key": list(fixed_outer_key),
        "search": {
            "internal_vertex_count": internal_vertex_count,
            "exact_patch_topology_count": exact_patch_topology_count,
            "patch_start_index": patch_start_index,
            "patch_topology_limit": patch_topology_limit,
            "next_patch_start_index": resume_patch_start_index,
            "next_radial_order_indices": list(resume_radial_order_indices),
            "slice_exhausted_exact_size_space": exhausted,
            "stopped_by_embedding_case_limit": stopped_by_embedding_case_limit,
            "embedding_case_limit": embedding_case_limit,
            "sampled_radial_order_indices": list(radial_order_indices),
            "max_rotation_systems_per_case": max_rotation_systems,
            "radial_face_coherence_condition": (
                "there exists a planar rotation system with all four radial "
                "cut edges on a single face of the cut-open collar graph"
            ),
            "patch_terminals": dict(PATCH_TERMINAL_VERTICES),
            "removed_parallel_edges": sorted(PATCH_REMOVED_PARALLEL_EDGES),
            "scan_rule": (
                "scan exact topology indices in order, require profile "
                "preservation first, skip structural normal-form blockers, "
                "and run the radial-face rotation audit only on the remaining "
                "planar/profile-preserving candidates"
            ),
        },
        "base_winding_profile_histogram": base_fiber["winding_profile_histogram"],
        "samples": samples,
        "summary": {
            "verdict": verdict,
            "processed_patch_topology_count": processed_patch_topology_count,
            "radial_order_case_count": radial_order_case_count,
            "profile_preserving_case_count": profile_preserving_case_count,
            "structural_skipped_case_count": structural_skipped_case_count,
            "embedding_audited_case_count": embedding_audited_case_count,
            "radial_face_coherent_case_count": radial_face_coherent_case_count,
            "radial_face_incoherent_case_count": radial_face_incoherent_case_count,
            "total_rotation_system_count": total_rotation_system_count,
            "enumerated_rotation_system_count": enumerated_rotation_system_count,
            "planar_rotation_system_count": planar_rotation_system_count,
            "radial_face_coherent_rotation_count":
                radial_face_coherent_rotation_count,
            "template_exclusion_blocker_histogram":
                dict(sorted(blocker_histogram.items())),
            "exact_template_histogram":
                dict(sorted(exact_template_histogram.items())),
            "max_radial_cut_edges_on_single_face_histogram":
                dict(sorted(max_radial_edges_histogram.items())),
        },
    }


def audit_closed_collar_winding_simple_patch_template_blockers(
    tau_states: list[tuple[str, ...]],
    internal_vertex_count: int,
    patch_start_index: int,
    patch_topology_limit: int,
    sample_limit: int,
) -> dict[str, object]:
    word = (TAU_TYPE, TAU_TYPE)
    fixed_outer_key = ("r", "r", "b", "b")
    base_model = build_closed_collar_model(word)
    base_fiber = audit_closed_collar_winding_fiber(
        word,
        fixed_outer_key,
        tau_states,
        include_all_components=True,
    )
    base_states = base_fiber.get("states", [])
    assert isinstance(base_states, list)
    if internal_vertex_count < 0 or internal_vertex_count % 2:
        raise ValueError("patch internal vertex count must be a nonnegative even number")
    if patch_start_index < 0:
        raise ValueError("patch start index must be nonnegative")
    if patch_topology_limit <= 0:
        raise ValueError("patch topology limit must be positive")

    processed_patch_topology_count = 0
    radial_order_case_count = 0
    profile_preserving_case_count = 0
    structural_first_blocker_count = 0
    exact_template_blocker_count = 0
    non_template_cyclic_cut_blocker_count = 0
    cap5_like_blocker_count = 0
    normal_form_after_template_exclusion_passing_count = 0
    first_blocker_histogram: Counter[str] = Counter()
    exact_template_histogram: Counter[str] = Counter()
    non_template_minimum_small_cut_histogram: Counter[str] = Counter()
    samples: list[dict[str, object]] = []
    sampled_blockers: set[str] = set()
    last_seen_patch_index: int | None = None
    exhausted = True

    for patch_index, patch_edges in enumerate(
        iter_simple_patch_edge_sets(internal_vertex_count)
    ):
        if patch_index < patch_start_index:
            continue
        if processed_patch_topology_count >= patch_topology_limit:
            exhausted = False
            break
        last_seen_patch_index = patch_index
        processed_patch_topology_count += 1

        model0, _patch_edge_names0, radial_edges0 = simple_patch_model(
            base_model,
            patch_edges,
        )
        radial_orders = (radial_edges0, tuple(reversed(radial_edges0)))
        for radial_order in radial_orders:
            radial_order_case_count += 1
            case_result = classify_simple_patch_template_blocker_case(
                base_model,
                base_states,
                patch_index,
                patch_edges,
                radial_order,
                sample_limit,
            )
            if case_result is None:
                continue
            profile_preserving_case_count += 1
            blocker_name = str(case_result["blocker_name"])
            first_blocker_histogram[blocker_name] += 1
            if blocker_name in STRUCTURAL_TEMPLATE_BLOCKERS:
                structural_first_blocker_count += 1
            elif blocker_name == "excluded_exact_diagonal_two_pole_template":
                template_key = case_result["exact_template_key"]
                assert isinstance(template_key, str)
                exact_template_blocker_count += 1
                exact_template_histogram[template_key] += 1
            elif blocker_name == "non_template_cyclic_edge_cut_of_size_at_most_four":
                minimum_small_cut = case_result["minimum_small_cut"]
                assert isinstance(minimum_small_cut, int)
                non_template_cyclic_cut_blocker_count += 1
                non_template_minimum_small_cut_histogram[str(minimum_small_cut)] += 1
            elif blocker_name == "cap5_free_literal_five_cycle_test":
                cap5_like_blocker_count += 1
            elif blocker_name == "none_after_template_exclusion":
                normal_form_after_template_exclusion_passing_count += 1
            else:
                raise AssertionError(blocker_name)
            add_template_blocker_sample(
                samples,
                sampled_blockers,
                sample_limit,
                case_result,
            )

    next_patch_start_index = patch_start_index + processed_patch_topology_count
    if exhausted and last_seen_patch_index is not None:
        next_patch_start_index = last_seen_patch_index + 1
    verdict = (
        "template_exclusion_slice_found_normal_form_prefix_realization"
        if normal_form_after_template_exclusion_passing_count
        else "template_exclusion_slice_found_non_template_cyclic_cut_blockers"
        if non_template_cyclic_cut_blocker_count
        else "template_exclusion_slice_blocked_by_structural_or_exact_template"
        if profile_preserving_case_count
        else "template_exclusion_slice_found_no_profile_preserving_patch"
    )
    return {
        "schema": "fourcolor-section-9-2-closed-collar-winding-simple-patch-template-blockers-v1",
        "source": (
            "Template-exclusion audit for profile-preserving simple patches in "
            "the closed-collar winding-freedom realization lab"
        ),
        "run_id": (
            f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}::"
            f"simple_patch_{internal_vertex_count}_template_blockers_from_"
            f"{patch_start_index}_limit_{patch_topology_limit}"
        ),
        "word": list(word_names(word)),
        "fixed_outer_key": list(fixed_outer_key),
        "search": {
            "internal_vertex_count": internal_vertex_count,
            "patch_start_index": patch_start_index,
            "patch_topology_limit": patch_topology_limit,
            "next_patch_start_index": next_patch_start_index,
            "slice_exhausted_exact_size_space": exhausted,
            "patch_terminals": dict(PATCH_TERMINAL_VERTICES),
            "removed_parallel_edges": sorted(PATCH_REMOVED_PARALLEL_EDGES),
            "excluded_template_keys": sorted(EXACT_DIAGONAL_COLLAR_TWO_POLE_TEMPLATE_KEYS),
            "classification": (
                "after profile preservation, first apply structural normal-form "
                "tests; if they pass, search directly for the exact diagonal "
                "two-pole cyclic-cut templates excluded by cyclic five-edge "
                "connectivity; only if no exact template is found, exhaustively "
                "check all small cyclic cuts and then the literal CAP5 test"
            ),
        },
        "base_winding_profile_histogram": base_fiber["winding_profile_histogram"],
        "samples": samples,
        "summary": {
            "verdict": verdict,
            "processed_patch_topology_count": processed_patch_topology_count,
            "radial_order_case_count": radial_order_case_count,
            "profile_preserving_case_count": profile_preserving_case_count,
            "structural_first_blocker_count": structural_first_blocker_count,
            "exact_template_blocker_count": exact_template_blocker_count,
            "non_template_cyclic_cut_blocker_count":
                non_template_cyclic_cut_blocker_count,
            "cap5_like_blocker_count": cap5_like_blocker_count,
            "normal_form_after_template_exclusion_passing_count":
                normal_form_after_template_exclusion_passing_count,
            "first_failed_after_template_exclusion_histogram":
                dict(sorted(first_blocker_histogram.items())),
            "exact_template_histogram":
                dict(sorted(exact_template_histogram.items())),
            "non_template_minimum_small_cyclic_cut_size_histogram":
                dict(sorted(non_template_minimum_small_cut_histogram.items())),
        },
    }


def audit_closed_collar_winding_simple_patch_template_blocker_index_sample(
    tau_states: list[tuple[str, ...]],
    internal_vertex_count: int,
    patch_indices: tuple[int, ...],
    sample_limit: int,
) -> dict[str, object]:
    word = (TAU_TYPE, TAU_TYPE)
    fixed_outer_key = ("r", "r", "b", "b")
    base_model = build_closed_collar_model(word)
    base_fiber = audit_closed_collar_winding_fiber(
        word,
        fixed_outer_key,
        tau_states,
        include_all_components=True,
    )
    base_states = base_fiber.get("states", [])
    assert isinstance(base_states, list)
    exact_patch_topology_count = simple_patch_edge_set_count(internal_vertex_count)
    if not patch_indices:
        raise ValueError("patch index sample must be nonempty")
    for patch_index in patch_indices:
        if patch_index < 0 or patch_index >= exact_patch_topology_count:
            raise ValueError(
                f"patch index {patch_index} is outside "
                f"[0, {exact_patch_topology_count})"
            )

    sampled_patch_topology_count = len(patch_indices)
    radial_order_case_count = 0
    profile_preserving_case_count = 0
    structural_first_blocker_count = 0
    exact_template_blocker_count = 0
    non_template_cyclic_cut_blocker_count = 0
    cap5_like_blocker_count = 0
    normal_form_after_template_exclusion_passing_count = 0
    first_blocker_histogram: Counter[str] = Counter()
    exact_template_histogram: Counter[str] = Counter()
    non_template_minimum_small_cut_histogram: Counter[str] = Counter()
    profile_failure_kind_histogram: Counter[str] = Counter()
    first_blocking_state_index_histogram: Counter[str] = Counter()
    wrong_profile_proper_extension_count_histogram: Counter[str] = Counter()
    wrong_profile_landed_profile_histogram: Counter[str] = Counter()
    samples: list[dict[str, object]] = []
    case_verdicts: list[dict[str, object]] = []
    sampled_blockers: set[str] = set()

    for patch_index in patch_indices:
        patch_edges = simple_patch_edge_set_at_index(
            internal_vertex_count,
            patch_index,
        )
        model0, _patch_edge_names0, radial_edges0 = simple_patch_model(
            base_model,
            patch_edges,
        )
        radial_orders = (radial_edges0, tuple(reversed(radial_edges0)))
        for radial_order_index, radial_order in enumerate(radial_orders):
            radial_order_case_count += 1
            model, patch_edge_names, radial_edges = simple_patch_model(
                base_model,
                patch_edges,
                radial_order,
            )
            first_profile_failure: dict[str, object] | None = None
            for state_payload in base_states:
                assert isinstance(state_payload, dict)
                raw_state = state_payload.get("state", {})
                desired_profile = state_payload.get("winding_profile", [])
                assert isinstance(raw_state, dict)
                assert isinstance(desired_profile, list)
                fixed_edge_colors = {
                    edge: str(raw_state[edge])
                    for edge in base_model.gadget.edges
                    if edge not in PATCH_REMOVED_PARALLEL_EDGES
                }
                diagnostic = simple_patch_profile_extension_diagnostic(
                    model,
                    patch_edge_names,
                    radial_edges,
                    fixed_edge_colors,
                    desired_profile,
                )
                if int(diagnostic["matching_profile_extension_count"]) == 0:
                    first_profile_failure = {
                        "first_blocking_state_index":
                            state_payload.get("state_index"),
                        **diagnostic,
                    }
                    break

            if first_profile_failure is not None:
                failure_kind = str(first_profile_failure["profile_failure_kind"])
                profile_failure_kind_histogram[failure_kind] += 1
                first_blocking_state_index_histogram[
                    str(first_profile_failure["first_blocking_state_index"])
                ] += 1
                if failure_kind == "proper_extensions_wrong_profile":
                    wrong_profile_proper_extension_count_histogram[
                        str(first_profile_failure["proper_tait_extension_count"])
                    ] += 1
                    landed_profiles = first_profile_failure[
                        "proper_tait_extension_profile_histogram"
                    ]
                    assert isinstance(landed_profiles, dict)
                    for profile_key, count in landed_profiles.items():
                        wrong_profile_landed_profile_histogram[str(profile_key)] += int(
                            count
                        )
                case_verdicts.append(
                    {
                        "patch_index": patch_index,
                        "patch_edge_count": len(patch_edges),
                        "radial_order_index": radial_order_index,
                        "radial_order": list(radial_order),
                        "profile_preserving": False,
                        "verdict": "no_profile_preserving_extension",
                        **first_profile_failure,
                    }
                )
                continue

            case_result = classify_simple_patch_template_blocker_case(
                base_model,
                base_states,
                patch_index,
                patch_edges,
                radial_order,
                sample_limit,
            )
            if case_result is None:
                raise AssertionError("profile diagnostic and classifier disagree")
            profile_preserving_case_count += 1
            blocker_name = str(case_result["blocker_name"])
            case_verdicts.append(
                {
                    "patch_index": patch_index,
                    "patch_edge_count": len(patch_edges),
                    "radial_order_index": radial_order_index,
                    "radial_order": list(radial_order),
                    "profile_preserving": True,
                    "verdict": blocker_name,
                }
            )
            first_blocker_histogram[blocker_name] += 1
            if blocker_name in STRUCTURAL_TEMPLATE_BLOCKERS:
                structural_first_blocker_count += 1
            elif blocker_name == "excluded_exact_diagonal_two_pole_template":
                template_key = case_result["exact_template_key"]
                assert isinstance(template_key, str)
                exact_template_blocker_count += 1
                exact_template_histogram[template_key] += 1
            elif blocker_name == "non_template_cyclic_edge_cut_of_size_at_most_four":
                minimum_small_cut = case_result["minimum_small_cut"]
                assert isinstance(minimum_small_cut, int)
                non_template_cyclic_cut_blocker_count += 1
                non_template_minimum_small_cut_histogram[str(minimum_small_cut)] += 1
            elif blocker_name == "cap5_free_literal_five_cycle_test":
                cap5_like_blocker_count += 1
            elif blocker_name == "none_after_template_exclusion":
                normal_form_after_template_exclusion_passing_count += 1
            else:
                raise AssertionError(blocker_name)
            add_template_blocker_sample(
                samples,
                sampled_blockers,
                sample_limit,
                case_result,
            )

    verdict = (
        "template_exclusion_index_sample_found_normal_form_prefix_realization"
        if normal_form_after_template_exclusion_passing_count
        else "template_exclusion_index_sample_found_non_template_cyclic_cut_blockers"
        if non_template_cyclic_cut_blocker_count
        else "template_exclusion_index_sample_blocked_by_structural_or_exact_template"
        if profile_preserving_case_count
        else "template_exclusion_index_sample_found_no_profile_preserving_patch"
    )
    return {
        "schema": (
            "fourcolor-section-9-2-closed-collar-winding-simple-patch-"
            "template-blocker-index-sample-v1"
        ),
        "source": (
            "Indexed-sample template-exclusion audit for profile-preserving "
            "simple patches in the closed-collar winding-freedom realization lab"
        ),
        "run_id": (
            f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}::"
            f"simple_patch_{internal_vertex_count}_template_blockers_"
            f"indexed_{sampled_patch_topology_count}"
        ),
        "word": list(word_names(word)),
        "fixed_outer_key": list(fixed_outer_key),
        "search": {
            "internal_vertex_count": internal_vertex_count,
            "exact_patch_topology_count": exact_patch_topology_count,
            "sampled_patch_indices": list(patch_indices),
            "sampled_patch_topology_count": sampled_patch_topology_count,
            "patch_terminals": dict(PATCH_TERMINAL_VERTICES),
            "removed_parallel_edges": sorted(PATCH_REMOVED_PARALLEL_EDGES),
            "excluded_template_keys": sorted(
                EXACT_DIAGONAL_COLLAR_TWO_POLE_TEMPLATE_KEYS
            ),
            "classification": (
                "for selected exact topology indices, unrank the simple cubic "
                "four-terminal patch and use the same template-exclusion "
                "classifier as the resumable slice audit"
            ),
        },
        "base_winding_profile_histogram": base_fiber["winding_profile_histogram"],
        "samples": samples,
        "case_verdicts": case_verdicts,
        "summary": {
            "verdict": verdict,
            "sampled_patch_topology_count": sampled_patch_topology_count,
            "radial_order_case_count": radial_order_case_count,
            "case_verdict_count": len(case_verdicts),
            "profile_preserving_case_count": profile_preserving_case_count,
            "no_profile_preserving_case_count":
                radial_order_case_count - profile_preserving_case_count,
            "structural_first_blocker_count": structural_first_blocker_count,
            "exact_template_blocker_count": exact_template_blocker_count,
            "non_template_cyclic_cut_blocker_count":
                non_template_cyclic_cut_blocker_count,
            "cap5_like_blocker_count": cap5_like_blocker_count,
            "normal_form_after_template_exclusion_passing_count":
                normal_form_after_template_exclusion_passing_count,
            "first_failed_after_template_exclusion_histogram":
                dict(sorted(first_blocker_histogram.items())),
            "profile_failure_kind_histogram":
                dict(sorted(profile_failure_kind_histogram.items())),
            "first_blocking_state_index_histogram":
                dict(sorted(first_blocking_state_index_histogram.items())),
            "wrong_profile_proper_extension_count_histogram":
                dict(sorted(wrong_profile_proper_extension_count_histogram.items())),
            "wrong_profile_landed_profile_histogram":
                dict(sorted(wrong_profile_landed_profile_histogram.items())),
            "exact_template_histogram":
                dict(sorted(exact_template_histogram.items())),
            "non_template_minimum_small_cyclic_cut_size_histogram":
                dict(sorted(non_template_minimum_small_cut_histogram.items())),
        },
    }


def audit_closed_collar_winding_k4_desingularization_witness(
    tau_states: list[tuple[str, ...]],
) -> dict[str, object]:
    word = (TAU_TYPE, TAU_TYPE)
    fixed_outer_key = ("r", "r", "b", "b")
    base_model = build_closed_collar_model(word)
    base_fiber = audit_closed_collar_winding_fiber(
        word,
        fixed_outer_key,
        tau_states,
        include_all_components=True,
    )
    states_payload = base_fiber.get("states", [])
    assert isinstance(states_payload, list)

    state_audits: list[dict[str, object]] = []
    graph_audit: dict[str, object] | None = None
    replacements: list[dict[str, object]] | None = None
    for state_payload in states_payload:
        assert isinstance(state_payload, dict)
        raw_state = state_payload.get("state", {})
        assert isinstance(raw_state, dict)
        state = tuple(str(raw_state[edge]) for edge in base_model.gadget.edges)
        desing_model, desing_state, replacement_payloads = (
            k4_desingularized_model_and_state(base_model, state)
        )
        if graph_audit is None:
            graph_audit = closed_collar_multigraph_audit(desing_model)
        if replacements is None:
            replacements = replacement_payloads
        original_profile = state_payload.get("winding_profile")
        desing_profile = closed_collar_profile_payload_for_model(
            desing_model,
            desing_state,
        )
        proper_payload = proper_state_check(desing_model.gadget, desing_state)
        state_audits.append(
            {
                "state_index": state_payload.get("state_index"),
                "proper_desingularized_coloring": proper_payload,
                "original_winding_profile": original_profile,
                "desingularized_winding_profile": desing_profile,
                "winding_profile_preserved": original_profile == desing_profile,
            }
        )

    assert graph_audit is not None
    assert replacements is not None
    first_blocker = graph_audit["first_failed_normal_form_test"]
    all_profiles_preserved = all(
        bool(state_audit["winding_profile_preserved"])
        for state_audit in state_audits
    )
    all_colorings_proper = all(
        bool(state_audit["proper_desingularized_coloring"]["proper"])
        for state_audit in state_audits
    )
    verdict = (
        "k4_desingularized_witness_passes_tested_normal_form_prefix"
        if first_blocker is None
        else f"k4_desingularized_witness_blocked_by_{first_blocker['name']}"
    )
    return {
        "schema": "fourcolor-section-9-2-closed-collar-winding-k4-desingularization-v1",
        "source": "Section 9.2 K4-two-pole desingularization audit for the closed-collar winding-freedom witness",
        "run_id": f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}",
        "word": list(word_names(word)),
        "fixed_outer_key": list(fixed_outer_key),
        "desingularization": {
            "rule": (
                "each two-edge parallel endpoint bundle is replaced by a "
                "simple cubic K4-minus-terminal-edge two-pole; terminal colors "
                "cross through the pole and the internal edge receives the third color"
            ),
            "radial_cut_lift": (
                "unreplaced closing edges remain on the radial cut; a replaced "
                "closing-edge pair lifts to the two terminal-side replacement edges"
            ),
            "replacement_bundles": replacements,
        },
        "base_winding_profile_histogram": base_fiber["winding_profile_histogram"],
        "state_audits": state_audits,
        "graph_audit": graph_audit,
        "summary": {
            "verdict": verdict,
            "all_desingularized_colorings_proper": all_colorings_proper,
            "all_winding_profiles_preserved": all_profiles_preserved,
            "first_failed_normal_form_test": first_blocker["name"] if first_blocker else None,
            "tested_normal_form_prefix_passed": [
                test["name"]
                for test in graph_audit["normal_form_tests"]
                if bool(test["passes"])
            ],
            "blocked_normal_form_tests": [
                test["name"]
                for test in graph_audit["normal_form_tests"]
                if not bool(test["passes"])
            ],
        },
    }


def audit_closed_collar_winding_realization_witness(
    tau_states: list[tuple[str, ...]],
) -> dict[str, object]:
    word = (TAU_TYPE, TAU_TYPE)
    fixed_outer_key = ("r", "r", "b", "b")
    model = build_closed_collar_model(word)
    winding_fiber = audit_closed_collar_winding_fiber(
        word,
        fixed_outer_key,
        tau_states,
        include_all_components=True,
    )
    graph_audit = closed_collar_multigraph_audit(model)
    witness_preserved = (
        not bool(winding_fiber["winding_data_boundary_determined"])
        and winding_fiber["proper_colorings"] > 0
    )
    first_blocker = graph_audit["first_failed_normal_form_test"]
    verdict = (
        "direct_witness_passes_tested_normal_form_prefix"
        if first_blocker is None
        else f"direct_witness_blocked_by_{first_blocker['name']}"
    )
    return {
        "schema": "fourcolor-section-9-2-closed-collar-winding-realization-witness-v1",
        "source": "Section 9.2 direct geometric realization audit for the closed-collar winding-freedom witness",
        "run_id": f"{word_key(word)}::{fixed_key_id(fixed_outer_key)}",
        "word": list(word_names(word)),
        "fixed_outer_key": list(fixed_outer_key),
        "model": {
            "tau_inputs": list(TAU_INPUT_ORDER),
            "tau_outputs": list(TAU_OUTPUT_ORDER),
            "closed_collar_rule": (
                "compose tau,tau cyclically by identifying the final ordered "
                "output stubs with the first ordered input stubs"
            ),
            "realization_scope": (
                "direct finite closed-collar witness graph; no filler expansion "
                "or subdivision search is claimed in this audit"
            ),
        },
        "winding_fiber": winding_fiber,
        "witness_profile_preserved": witness_preserved,
        "graph_audit": graph_audit,
        "summary": {
            "verdict": verdict,
            "witness_profile_preserved": witness_preserved,
            "first_failed_normal_form_test": first_blocker["name"] if first_blocker else None,
            "tested_normal_form_prefix_passed": [
                test["name"]
                for test in graph_audit["normal_form_tests"]
                if bool(test["passes"])
            ],
            "blocked_normal_form_tests": [
                test["name"]
                for test in graph_audit["normal_form_tests"]
                if not bool(test["passes"])
            ],
        },
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


def refresh_winding_summary(report: dict[str, object]) -> None:
    fibers = report.get("fibers", [])
    assert isinstance(fibers, list)
    planned = report.get("planned_fiber_count", 0)
    assert isinstance(planned, int)
    freedom = [
        fiber for fiber in fibers
        if not fiber.get("winding_data_boundary_determined")
    ]
    first = freedom[0] if freedom else None
    report["summary"] = {
        "planned_fiber_count": planned,
        "completed_fiber_count": len(fibers),
        "remaining_fiber_count": max(0, planned - len(fibers)),
        "word_count": len({tuple(fiber.get("word", [])) for fiber in fibers}),
        "nonempty_fiber_count": sum(1 for fiber in fibers if not fiber.get("empty_fiber")),
        "empty_fiber_count": sum(1 for fiber in fibers if fiber.get("empty_fiber")),
        "boundary_determined_fiber_count": sum(
            1 for fiber in fibers if fiber.get("winding_data_boundary_determined")
        ),
        "winding_freedom_fiber_count": len(freedom),
        "all_completed_fibers_boundary_determined": not freedom,
        "complete": len(fibers) == planned,
        "first_winding_freedom_run_id": first.get("run_id") if isinstance(first, dict) else None,
        "first_winding_freedom_witness": (
            first.get("first_winding_freedom_witness") if isinstance(first, dict) else None
        ),
        "verdict": (
            "not_boundary_determined"
            if freedom
            else ("boundary_determined" if len(fibers) == planned else "incomplete")
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


def new_closed_collar_winding_report(
    tau_state_count: int,
    include_all_components: bool,
) -> dict[str, object]:
    words = closed_collar_l1_words()
    planned_fiber_count = sum(3 ** 4 for _ in words)
    report: dict[str, object] = {
        "schema": "fourcolor-section-9-2-closed-collar-winding-l1-v2",
        "source": "Section 9.2 closed-collar length-2/3 winding-invariant lab",
        "model": {
            "tau_inputs": list(TAU_INPUT_ORDER),
            "tau_outputs": list(TAU_OUTPUT_ORDER),
            "mirror_tau_inputs": list(MIRROR_TAU_TYPE.input_order),
            "mirror_tau_outputs": list(MIRROR_TAU_TYPE.output_order),
            "closed_collar_rule": (
                "compose a length-2 or length-3 word cyclically by identifying "
                "the final ordered output stubs with the first ordered input stubs"
            ),
            "fixed_outer_fiber": "one four-color key on the closing edges is fixed per run",
            "radial_cut": "the same closing edges, used as the fixed radial cut",
            "winding_rule": (
                "for each two-color component, take the crossing count with the "
                "radial cut modulo 2"
            ),
            "tested_boundary_datum": (
                "the per-color-pair multiset of component winding classes, recorded "
                "as winding0 and winding1 component counts"
            ),
        },
        "local_tau_state_count": tau_state_count,
        "word_lengths": [2, 3],
        "planned_words": [list(word_names(word)) for word in words],
        "planned_word_count": len(words),
        "planned_fiber_count": planned_fiber_count,
        "include_all_state_component_payloads": include_all_components,
        "fibers": [],
    }
    refresh_winding_summary(report)
    return report


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


def run_closed_collar_winding_l1(
    output: Path | None,
    resume: bool,
    continue_after_freedom: bool,
    include_all_components: bool,
) -> dict[str, object]:
    tau_states = proper_states(TAU)
    if resume and output is not None and output.exists():
        report = json.loads(output.read_text())
        report.setdefault("fibers", [])
    else:
        report = new_closed_collar_winding_report(
            len(tau_states),
            include_all_components,
        )

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
            fiber = audit_closed_collar_winding_fiber(
                word,
                key,
                tau_states,
                include_all_components,
            )
            fibers.append(fiber)
            done.add(run_id)
            refresh_winding_summary(report)
            if output is not None:
                write_json_report(output, report)
            if (
                not fiber["winding_data_boundary_determined"]
                and not continue_after_freedom
            ):
                return report

    refresh_winding_summary(report)
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_winding_realization_witness(
    output: Path | None,
    resume: bool,
) -> dict[str, object]:
    if resume and output is not None and output.exists():
        return json.loads(output.read_text())

    report = audit_closed_collar_winding_realization_witness(proper_states(TAU))
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_winding_k4_desingularization_witness(
    output: Path | None,
    resume: bool,
) -> dict[str, object]:
    if resume and output is not None and output.exists():
        return json.loads(output.read_text())

    report = audit_closed_collar_winding_k4_desingularization_witness(proper_states(TAU))
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_winding_simple_patch_search(
    output: Path | None,
    resume: bool,
    max_internal_vertices: int,
    sample_limit: int,
) -> dict[str, object]:
    if resume and output is not None and output.exists():
        return json.loads(output.read_text())

    report = audit_closed_collar_winding_simple_patch_search(
        proper_states(TAU),
        max_internal_vertices=max_internal_vertices,
        sample_limit=sample_limit,
    )
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_winding_simple_patch_slice(
    output: Path | None,
    resume: bool,
    internal_vertex_count: int,
    patch_start_index: int,
    patch_topology_limit: int,
    sample_limit: int,
) -> dict[str, object]:
    if resume and output is not None and output.exists():
        return json.loads(output.read_text())

    report = audit_closed_collar_winding_simple_patch_slice(
        proper_states(TAU),
        internal_vertex_count=internal_vertex_count,
        patch_start_index=patch_start_index,
        patch_topology_limit=patch_topology_limit,
        sample_limit=sample_limit,
    )
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_winding_simple_patch_cyclic_cut_shapes(
    output: Path | None,
    resume: bool,
    internal_vertex_count: int,
    patch_start_index: int,
    patch_topology_limit: int,
    sample_limit: int,
) -> dict[str, object]:
    if resume and output is not None and output.exists():
        return json.loads(output.read_text())

    report = audit_closed_collar_winding_simple_patch_cyclic_cut_shapes(
        proper_states(TAU),
        internal_vertex_count=internal_vertex_count,
        patch_start_index=patch_start_index,
        patch_topology_limit=patch_topology_limit,
        sample_limit=sample_limit,
    )
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_winding_simple_patch_template_blockers(
    output: Path | None,
    resume: bool,
    internal_vertex_count: int,
    patch_start_index: int,
    patch_topology_limit: int,
    sample_limit: int,
) -> dict[str, object]:
    if resume and output is not None and output.exists():
        return json.loads(output.read_text())

    report = audit_closed_collar_winding_simple_patch_template_blockers(
        proper_states(TAU),
        internal_vertex_count=internal_vertex_count,
        patch_start_index=patch_start_index,
        patch_topology_limit=patch_topology_limit,
        sample_limit=sample_limit,
    )
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_winding_simple_patch_template_blocker_index_sample(
    output: Path | None,
    resume: bool,
    internal_vertex_count: int,
    patch_indices: tuple[int, ...],
    sample_limit: int,
) -> dict[str, object]:
    if resume and output is not None and output.exists():
        return json.loads(output.read_text())

    report = audit_closed_collar_winding_simple_patch_template_blocker_index_sample(
        proper_states(TAU),
        internal_vertex_count=internal_vertex_count,
        patch_indices=patch_indices,
        sample_limit=sample_limit,
    )
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_winding_simple_patch_annular_embedding_sample(
    output: Path | None,
    resume: bool,
    internal_vertex_count: int,
    patch_indices: tuple[int, ...],
    radial_order_indices: tuple[int, ...],
    sample_limit: int,
    max_rotation_systems: int,
) -> dict[str, object]:
    if resume and output is not None and output.exists():
        return json.loads(output.read_text())

    report = audit_closed_collar_winding_simple_patch_annular_embedding_sample(
        proper_states(TAU),
        internal_vertex_count=internal_vertex_count,
        patch_indices=patch_indices,
        radial_order_indices=radial_order_indices,
        sample_limit=sample_limit,
        max_rotation_systems=max_rotation_systems,
    )
    if output is not None:
        write_json_report(output, report)
    return report


def run_closed_collar_winding_simple_patch_annular_embedding_slice(
    output: Path | None,
    resume: bool,
    internal_vertex_count: int,
    patch_start_index: int,
    patch_topology_limit: int,
    radial_order_indices: tuple[int, ...],
    sample_limit: int,
    max_rotation_systems: int,
    embedding_case_limit: int,
) -> dict[str, object]:
    if resume and output is not None and output.exists():
        return json.loads(output.read_text())

    report = audit_closed_collar_winding_simple_patch_annular_embedding_slice(
        proper_states(TAU),
        internal_vertex_count=internal_vertex_count,
        patch_start_index=patch_start_index,
        patch_topology_limit=patch_topology_limit,
        radial_order_indices=radial_order_indices,
        sample_limit=sample_limit,
        max_rotation_systems=max_rotation_systems,
        embedding_case_limit=embedding_case_limit,
    )
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
        "--closed-collar-winding-l1",
        action="store_true",
        help="run the cyclic length-2/3 closed-collar winding-invariant lab",
    )
    parser.add_argument(
        "--closed-collar-winding-realization-witness",
        action="store_true",
        help="audit the direct tau,tau::rrbb winding-freedom witness against geometric normal-form tests",
    )
    parser.add_argument(
        "--closed-collar-winding-k4-desingularization-witness",
        action="store_true",
        help="audit the K4-two-pole desingularized tau,tau::rrbb winding-freedom witness",
    )
    parser.add_argument(
        "--closed-collar-winding-simple-patch-search",
        action="store_true",
        help=(
            "search bounded simple cubic four-terminal patches for the "
            "tau,tau::rrbb winding-freedom witness"
        ),
    )
    parser.add_argument(
        "--closed-collar-winding-simple-patch-slice",
        action="store_true",
        help=(
            "run one exact-size slice of the simple cubic four-terminal patch "
            "search for the tau,tau::rrbb winding-freedom witness"
        ),
    )
    parser.add_argument(
        "--closed-collar-winding-simple-patch-cyclic-cut-shapes",
        action="store_true",
        help=(
            "run one exact-size slice and classify first cyclic-cut blockers "
            "among profile-preserving simple patches"
        ),
    )
    parser.add_argument(
        "--closed-collar-winding-simple-patch-template-blockers",
        action="store_true",
        help=(
            "run one exact-size slice and classify whether profile-preserving "
            "simple patches are blocked by structural tests, the exact excluded "
            "diagonal two-pole templates, or a residual normal-form condition"
        ),
    )
    parser.add_argument(
        "--closed-collar-winding-simple-patch-template-blocker-index-sample",
        action="store_true",
        help=(
            "run an indexed sample of exact-size simple patches through the "
            "same template-exclusion classifier"
        ),
    )
    parser.add_argument(
        "--closed-collar-winding-simple-patch-annular-embedding-sample",
        action="store_true",
        help=(
            "run an indexed sample of profile-preserving simple patches through "
            "the radial-face annular embedding coherence audit"
        ),
    )
    parser.add_argument(
        "--closed-collar-winding-simple-patch-annular-embedding-slice",
        action="store_true",
        help=(
            "scan a bounded exact-size simple-patch slice and run the "
            "radial-face annular embedding coherence audit on discovered "
            "profile-preserving non-structural cases"
        ),
    )
    parser.add_argument(
        "--max-patch-internal-vertices",
        type=int,
        default=4,
        help="maximum internal patch vertices for --closed-collar-winding-simple-patch-search",
    )
    parser.add_argument(
        "--patch-internal-vertices",
        type=int,
        default=6,
        help="exact internal patch vertex count for --closed-collar-winding-simple-patch-slice",
    )
    parser.add_argument(
        "--patch-start-index",
        type=int,
        default=0,
        help="zero-based patch topology index where --closed-collar-winding-simple-patch-slice starts",
    )
    parser.add_argument(
        "--patch-topology-limit",
        type=int,
        default=50000,
        help="maximum patch topologies processed by --closed-collar-winding-simple-patch-slice",
    )
    parser.add_argument(
        "--patch-candidate-sample-limit",
        type=int,
        default=12,
        help="number of profile-preserving patch candidates to include as detailed samples",
    )
    parser.add_argument(
        "--patch-indices",
        help=(
            "comma-separated exact topology indices for "
            "--closed-collar-winding-simple-patch-template-blocker-index-sample"
        ),
    )
    parser.add_argument(
        "--patch-radial-order-indices",
        help=(
            "comma-separated radial order indices, 0 or 1, for "
            "--closed-collar-winding-simple-patch-annular-embedding-sample; "
            "defaults to both orders"
        ),
    )
    parser.add_argument(
        "--patch-stratified-sample-count",
        type=int,
        default=33,
        help=(
            "number of evenly stratified exact topology indices to sample when "
            "--patch-indices is omitted"
        ),
    )
    parser.add_argument(
        "--embedding-rotation-system-limit",
        type=int,
        default=300000,
        help=(
            "maximum combinatorial rotation systems per case for "
            "--closed-collar-winding-simple-patch-annular-embedding-sample"
        ),
    )
    parser.add_argument(
        "--embedding-case-limit",
        type=int,
        default=1,
        help=(
            "maximum profile-preserving non-structural cases audited by "
            "--closed-collar-winding-simple-patch-annular-embedding-slice"
        ),
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
    parser.add_argument(
        "--continue-after-winding-freedom",
        action="store_true",
        help="continue --closed-collar-winding-l1 after the first non-boundary-determined fiber",
    )
    parser.add_argument(
        "--include-winding-components",
        action="store_true",
        help="include full component payloads for every state in --closed-collar-winding-l1",
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

    if args.closed_collar_winding_l1:
        report = run_closed_collar_winding_l1(
            output=args.output,
            resume=args.resume,
            continue_after_freedom=args.continue_after_winding_freedom,
            include_all_components=args.include_winding_components,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        summary = report.get("summary", {})
        if isinstance(summary, dict) and summary.get("winding_freedom_fiber_count"):
            raise SystemExit(2)
        return

    if args.closed_collar_winding_realization_witness:
        report = run_closed_collar_winding_realization_witness(
            output=args.output,
            resume=args.resume,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return

    if args.closed_collar_winding_k4_desingularization_witness:
        report = run_closed_collar_winding_k4_desingularization_witness(
            output=args.output,
            resume=args.resume,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return

    if args.closed_collar_winding_simple_patch_search:
        report = run_closed_collar_winding_simple_patch_search(
            output=args.output,
            resume=args.resume,
            max_internal_vertices=args.max_patch_internal_vertices,
            sample_limit=args.patch_candidate_sample_limit,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return

    if args.closed_collar_winding_simple_patch_slice:
        report = run_closed_collar_winding_simple_patch_slice(
            output=args.output,
            resume=args.resume,
            internal_vertex_count=args.patch_internal_vertices,
            patch_start_index=args.patch_start_index,
            patch_topology_limit=args.patch_topology_limit,
            sample_limit=args.patch_candidate_sample_limit,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return

    if args.closed_collar_winding_simple_patch_cyclic_cut_shapes:
        report = run_closed_collar_winding_simple_patch_cyclic_cut_shapes(
            output=args.output,
            resume=args.resume,
            internal_vertex_count=args.patch_internal_vertices,
            patch_start_index=args.patch_start_index,
            patch_topology_limit=args.patch_topology_limit,
            sample_limit=args.patch_candidate_sample_limit,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return

    if args.closed_collar_winding_simple_patch_template_blockers:
        report = run_closed_collar_winding_simple_patch_template_blockers(
            output=args.output,
            resume=args.resume,
            internal_vertex_count=args.patch_internal_vertices,
            patch_start_index=args.patch_start_index,
            patch_topology_limit=args.patch_topology_limit,
            sample_limit=args.patch_candidate_sample_limit,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return

    if args.closed_collar_winding_simple_patch_template_blocker_index_sample:
        if args.patch_indices:
            patch_indices = parse_patch_index_list(args.patch_indices)
        else:
            exact_count = simple_patch_edge_set_count(args.patch_internal_vertices)
            patch_indices = stratified_patch_indices(
                exact_count,
                args.patch_stratified_sample_count,
            )
        report = run_closed_collar_winding_simple_patch_template_blocker_index_sample(
            output=args.output,
            resume=args.resume,
            internal_vertex_count=args.patch_internal_vertices,
            patch_indices=patch_indices,
            sample_limit=args.patch_candidate_sample_limit,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return

    if args.closed_collar_winding_simple_patch_annular_embedding_sample:
        if args.patch_indices:
            patch_indices = parse_patch_index_list(args.patch_indices)
        else:
            exact_count = simple_patch_edge_set_count(args.patch_internal_vertices)
            patch_indices = stratified_patch_indices(
                exact_count,
                args.patch_stratified_sample_count,
            )
        if args.patch_radial_order_indices:
            radial_order_indices = parse_patch_index_list(
                args.patch_radial_order_indices
            )
        else:
            radial_order_indices = (0, 1)
        report = run_closed_collar_winding_simple_patch_annular_embedding_sample(
            output=args.output,
            resume=args.resume,
            internal_vertex_count=args.patch_internal_vertices,
            patch_indices=patch_indices,
            radial_order_indices=radial_order_indices,
            sample_limit=args.patch_candidate_sample_limit,
            max_rotation_systems=args.embedding_rotation_system_limit,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return

    if args.closed_collar_winding_simple_patch_annular_embedding_slice:
        if args.patch_radial_order_indices:
            radial_order_indices = parse_patch_index_list(
                args.patch_radial_order_indices
            )
        else:
            radial_order_indices = (0, 1)
        report = run_closed_collar_winding_simple_patch_annular_embedding_slice(
            output=args.output,
            resume=args.resume,
            internal_vertex_count=args.patch_internal_vertices,
            patch_start_index=args.patch_start_index,
            patch_topology_limit=args.patch_topology_limit,
            radial_order_indices=radial_order_indices,
            sample_limit=args.patch_candidate_sample_limit,
            max_rotation_systems=args.embedding_rotation_system_limit,
            embedding_case_limit=args.embedding_case_limit,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
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
