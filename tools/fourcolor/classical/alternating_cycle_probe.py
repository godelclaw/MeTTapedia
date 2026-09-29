#!/usr/bin/env python3
"""Enumerate alternating-turn orbits and recognize actual open rows.

These are independent finite program checks, not Lean certificates. Every
dart and turn phase is inspected. Repeated-vertex orbits are retained as
negative controls; a finite permutation orbit need not be a simple cycle.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

import networkx as nx

from hexagonal_collar_probe import (
    capped_rotation, cycles, graph_rotation, make_goldberg_graph,
)


def alternating_orbits(alpha, rho):
    step = {(d, phase): ((rho[alpha[d]] if phase == 0 else rho[rho[alpha[d]]]),
                         1 - phase)
            for d in alpha for phase in (0, 1)}
    assert set(step) == set(step.values())
    result = cycles(step)
    assert sum(map(len, result)) == len(step)
    return result


def oriented_row(graph, rho, orbit):
    row = tuple(d[0] for d, _ in orbit)
    if len(set(row)) != len(row):
        return None
    assert len(row) % 2 == 0 and len(row) >= 4
    assert graph.subgraph(row).number_of_edges() == len(row)
    third = {u: next(iter(set(graph[u]) - set(row))) for u in row}
    incoming = [rho[u, third[u]] == (u, row[(i + 1) % len(row)])
                for i, u in enumerate(row)]
    assert all(incoming[i] != incoming[(i + 1) % len(row)] for i in range(len(row)))
    return row if incoming[0] else row[1:] + row[:1]


def grow(graph, alpha, rho, face_of, row):
    width = len(row) // 2
    third = lambda u, r: next(iter(set(graph[u]) - set(r)))
    remainder = graph.subgraph(set(graph) - set(row))
    inner = set(nx.node_connected_component(remainder, third(row[0], row)))
    side = inner | set(row)
    history = []

    def boundary(vertices):
        return {d for d in alpha if d[0] in vertices and d[1] not in vertices}

    while True:
        assert len(history) <= len(graph)
        inputs = [(row[2 * i], third(row[2 * i], row)) for i in range(width)]
        outputs = [(row[2 * i + 1], third(row[2 * i + 1], row)) for i in range(width)]
        assert boundary(inner) == {alpha[d] for d in inputs}
        assert boundary(side) == set(outputs)
        assert all(rho[d] == (row[2 * i], row[2 * i + 1])
                   for i, d in enumerate(inputs))
        assert all(rho[d] == (row[2 * i + 1], row[2 * i])
                   for i, d in enumerate(outputs))
        history.append(row)
        pentagonal = [face_of[d] for d in outputs if len(face_of[d]) == 5]
        if pentagonal:
            return {"width": width, "successful_extensions": len(history) - 1,
                    "rows": history, "terminal_pentagonal_face": pentagonal[0],
                    "terminal_pentagonal_port_incidences": len(pentagonal)}
        assert all(len(face_of[d]) == 6 for d in outputs)
        x = [alpha[d] for d in outputs]
        y = [alpha[rho[d]] for d in x]
        new_row = tuple(v for i in range(width) for v in (x[i][0], y[i][0]))
        assert len(set(new_row)) == 2 * width
        assert not side & set(new_row)
        assert all(graph.has_edge(new_row[i], new_row[(i + 1) % len(new_row)])
                   for i in range(len(new_row)))
        assert graph.subgraph(new_row).number_of_edges() == 2 * width
        inner, side, row = side, side | set(new_row), new_row


def inspect(name, graph, alpha, rho):
    assert len(alpha) == 2 * graph.number_of_edges()
    assert set(alpha) == set(rho) == {(u, v) for u in graph for v in graph[u]}
    assert all(graph.degree(v) == 3 for v in graph)
    assert all(alpha[alpha[d]] == d and alpha[d] != d for d in alpha)
    assert all(rho[rho[rho[d]]] == d and rho[d] != d and rho[d][0] == d[0] for d in rho)
    faces = cycles({d: rho[alpha[d]] for d in alpha})
    assert all(len(face) in (5, 6) for face in faces)
    assert len(graph) - graph.number_of_edges() + len(faces) == 2
    assert nx.is_connected(graph) and not list(nx.bridges(graph))
    face_of = {d: face for face in faces for d in face}
    histories, nonsimple = [], []
    orbits = alternating_orbits(alpha, rho)
    for orbit in orbits:
        row = oriented_row(graph, rho, orbit)
        if row is None:
            vertices = [d[0] for d, _ in orbit]
            seen = {}
            for i, v in enumerate(vertices):
                if v in seen:
                    nonsimple.append({"orbit_length": len(orbit),
                                      "repeated_vertex": v,
                                      "positions": [seen[v], i],
                                      "orbit_prefix": orbit[:i + 1]})
                    break
                seen[v] = i
        else:
            histories.append(grow(graph, alpha, rho, face_of, row))
    assert len(orbits) == len(histories) + len(nonsimple)
    serial = sorted((list(d), list(rho[d])) for d in rho)
    return {"map": name, "vertices": len(graph), "edges": graph.number_of_edges(),
            "face_lengths": dict(sorted(Counter(map(len, faces)).items())),
            "rotation_sha256": hashlib.sha256(json.dumps(serial).encode()).hexdigest(),
            "dart_phase_states": 2 * len(alpha),
            "orbit_length_histogram": dict(sorted(Counter(map(len, orbits)).items())),
            "simple_oriented_rows": len(histories),
            "width_histogram": dict(sorted(Counter(h["width"] for h in histories).items())),
            "extension_histogram": dict(sorted(Counter(h["successful_extensions"] for h in histories).items())),
            "total_successful_extensions": sum(h["successful_extensions"] for h in histories),
            "pentagonal_endpoints": len(histories),
            "nonsimple_orbits": len(nonsimple),
            "nonsimple_witness": nonsimple[0] if nonsimple else None,
            "longest_history": max(histories, key=lambda h: h["successful_extensions"], default=None)}


def run():
    examples = []
    for shifts in ([0, 0], [2, 4], [2, 4, 1, 3], [4, 2, 3, 1, 4, 2]):
        examples.append(inspect(f"capped strip shifts {shifts}", *capped_rotation(shifts)))
    for frequency in range(1, 9):
        data = make_goldberg_graph(frequency)
        examples.append(inspect(f"Goldberg GP({frequency},0)",
                                *graph_rotation(data["primal_edges"])))
    return {"evidence": "Independent finite program checks, not Lean certificates.",
            "scope": "All dart/phase orbits of the twelve displayed rotations; no cycle-length cutoff.",
            "state_step": "Cross the edge and alternate one and two positive vertex rotations; flip the phase.",
            "controls": ["Simple orbits are checked as induced cycles with both complete shore boundaries.",
                         "Every successful extension retains the same width and uses fresh original vertices.",
                         "Non-simple orbits are recorded and not promoted to rows.",
                         "The Goldberg observations are finite; no all-frequency theorem or universal row-supply theorem is asserted.",
                         "The width-five four-ring bound is not applied to wider rows."],
            "examples": examples}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps([{k: e[k] for k in ("map", "simple_oriented_rows", "width_histogram",
                                       "extension_histogram", "nonsimple_orbits")}
                      for e in result["examples"]], indent=2))
