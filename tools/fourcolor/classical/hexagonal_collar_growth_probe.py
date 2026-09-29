#!/usr/bin/env python3
"""Check complete collar-growth histories in explicit spherical cubic maps.

Every recognized oriented five-port row is followed through its actual
surrounding hexagons to a pentagonal seam. These are independent finite
program checks, separate from the general Lean noncollision proof.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

import networkx as nx

from hexagonal_collar_probe import (
    capped_rotation, cycles, graph_rotation, make_goldberg_graph, ten_cycles,
)


def recognize(graph, rho, cycle):
    third = {u: next(iter(set(graph[u]) - set(cycle))) for u in cycle
             if len(set(graph[u]) - set(cycle)) == 1}
    if len(third) != 10:
        return None
    incoming = [rho[u, third[u]] == (u, cycle[(i + 1) % 10])
                for i, u in enumerate(cycle)]
    if any(incoming[i] == incoming[(i + 1) % 10] for i in range(10)):
        return None
    return tuple(cycle if incoming[0] else cycle[1:] + cycle[:1])


def grow(graph, alpha, rho, face_of, row):
    third = lambda u, r: next(iter(set(graph[u]) - set(r)))
    remainder = graph.subgraph(set(graph) - set(row))
    inner = set(nx.node_connected_component(remainder, third(row[0], row)))
    old_side = inner | set(row)
    rows = []

    def boundary(side):
        return {d for d in alpha if d[0] in side and d[1] not in side}

    while True:
        assert len(rows) <= len(graph)
        assert recognize(graph, rho, row) == row
        rows.append(row)
        inputs = [(row[2 * i], third(row[2 * i], row)) for i in range(5)]
        outputs = [(row[2 * i + 1], third(row[2 * i + 1], row)) for i in range(5)]
        assert boundary(old_side - set(row)) == {alpha[d] for d in inputs}
        assert boundary(old_side) == set(outputs)
        assert all(len(face_of[d]) in (5, 6) for d in outputs)
        pentagons = [face_of[d] for d in outputs if len(face_of[d]) == 5]
        if pentagons:
            return {"successful_extensions": len(rows) - 1,
                    "rows": rows, "terminal_pentagonal_face": pentagons[0],
                    "final_side_vertices": len(old_side)}
        x = [alpha[d] for d in outputs]
        y = [alpha[rho[d]] for d in x]
        next_row = tuple(v for i in range(5) for v in (x[i][0], y[i][0]))
        assert len(set(next_row)) == 10
        assert not (old_side & set(next_row))
        assert all(graph.has_edge(next_row[i], next_row[(i + 1) % 10])
                   for i in range(10))
        assert graph.subgraph(next_row).number_of_edges() == 10
        new_outputs = {rho[rho[d]] for d in y}
        new_side = old_side | set(next_row)
        assert len(new_side) == len(old_side) + 10
        assert boundary(new_side) == new_outputs
        old_side, row = new_side, next_row


def inspect(name, graph, alpha, rho):
    assert all(graph.degree(v) == 3 for v in graph)
    assert len(alpha) == 2 * graph.number_of_edges()
    phi = {d: rho[alpha[d]] for d in alpha}
    faces = cycles(phi)
    face_of = {d: face for face in faces for d in face}
    assert all(len(face) in (5, 6) for face in faces)
    assert len(graph) - graph.number_of_edges() + len(faces) == 2
    assert nx.is_connected(graph) and not list(nx.bridges(graph))
    histories = []
    for cycle in ten_cycles(graph):
        for orientation in (cycle, cycle[::-1]):
            row = recognize(graph, rho, orientation)
            if row is not None:
                histories.append(grow(graph, alpha, rho, face_of, row))
    counts = Counter(h["successful_extensions"] for h in histories)
    return {"map": name, "vertices": len(graph),
            "recognized_oriented_starts": len(histories),
            "pentagonal_endpoints": len(histories),
            "extension_histogram": dict(sorted(counts.items())),
            "longest_history": max(histories, key=lambda h: h["successful_extensions"],
                                   default=None)}


def run():
    examples = []
    for shifts in ([0, 0], [2, 4], [2, 4, 1, 3], [4, 2, 3, 1, 4, 2]):
        examples.append(inspect(f"capped strip shifts {shifts}", *capped_rotation(shifts)))
    for frequency in (1, 2, 3):
        data = make_goldberg_graph(frequency)
        examples.append(inspect(f"Goldberg GP({frequency},0)",
                                *graph_rotation(data["primal_edges"])))
    return {"evidence": "Independent finite program checks, not Lean certificates.",
            "scope": "All recognized oriented five-port rows in these seven maps.",
            "controls": ["Each step checks both complete boundaries, orientation and ten fresh vertices.",
                         "Every recorded endpoint is an actual pentagonal face.",
                         "The three-extension theorem assumes minimal counterexample status; this probe checks finite growth without that assumption.",
                         "Maps with no starting row remain in the report."],
            "examples": examples}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps([{k: e[k] for k in ("map", "recognized_oriented_starts",
                                       "extension_histogram")}
                      for e in result["examples"]], indent=2))
