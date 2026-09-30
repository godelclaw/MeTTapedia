#!/usr/bin/env python3
"""Replay the cube cut consumer and a separator diagnostic independently.

The cube comes from the same flat rotation data used by the Lean consumer.
All vertex sides and pair deletions are checked. A cubic graph with a bridge
shows why a cut hypothesis is needed. These are program checks; the general
cut theorem and the cube's boundary interpretation are proved in Lean.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re

import networkx as nx

from coupled_source_colouring_probe import structural_colouring

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def cube():
    text = (LEAN / "DualTruncateCoupledExample.lean").read_text()
    table = re.search(r"neighbours\s*:=.*?ByteArray\.mk\s*#\[(.*?)\]", text, re.S)
    assert table
    flat = bytes(map(int, re.findall(r"\d+", table.group(1))))
    neighbours = [int.from_bytes(flat[i:i + 2], "little") for i in range(0, len(flat), 2)]
    assert len(neighbours) == 24
    rows = [neighbours[i:i + 3] for i in range(0, 24, 3)]
    graph = nx.Graph()
    graph.add_nodes_from(range(8))
    graph.add_edges_from((v, w) for v, row in enumerate(rows) for w in row)
    assert all(len(set(row)) == 3 for row in rows)
    assert all(v in rows[w] for v, row in enumerate(rows) for w in row)
    return graph


def small_cyclic_cuts(graph):
    vertices = sorted(graph)
    result = []
    for mask in range(1, (1 << len(vertices)) - 1):
        if not mask & 1:
            continue
        side = {v for i, v in enumerate(vertices) if mask >> i & 1}
        outside = set(vertices) - side
        boundary = sum((u in side) != (v in side) for u, v in graph.edges())
        if boundary <= 3 and nx.cycle_basis(graph.subgraph(side)) and nx.cycle_basis(graph.subgraph(outside)):
            result.append(dict(side=sorted(side), boundary=boundary))
    return result


def run():
    graph = cube()
    assert all(d == 3 for _, d in graph.degree()) and nx.is_connected(graph)
    bounds = []
    for mask in range(1 << len(graph)):
        side = {v for v in graph if mask >> v & 1}
        if 2 <= len(side) <= len(graph) - 2:
            boundary = sum((u in side) != (v in side) for u, v in graph.edges())
            assert boundary >= 4
            bounds.append(boundary)
    cuts = small_cyclic_cuts(graph)
    assert not cuts
    pairs = list(itertools.combinations(graph, 2))
    assert all(nx.is_connected(graph.subgraph(set(graph) - set(pair))) for pair in pairs)
    initial, order, colours, maximum = structural_colouring(graph)
    # Subdivide an edge in each of two K4s and join the new vertices.
    diagnostic = nx.disjoint_union(nx.complete_graph(4), nx.complete_graph(4))
    diagnostic.remove_edges_from([(0, 1), (4, 5)])
    diagnostic.add_edges_from([(0, 8), (8, 1), (4, 9), (9, 5), (8, 9)])
    assert nx.is_connected(diagnostic) and all(d == 3 for _, d in diagnostic.degree())
    assert not nx.is_connected(diagnostic.subgraph(set(diagnostic) - {8, 9}))
    diagnostic_cuts = small_cyclic_cuts(diagnostic)
    assert any(cut["boundary"] == 1 for cut in diagnostic_cuts)
    paths = [Path(__file__), HERE / "coupled_source_colouring_probe.py",
             LEAN / "DualTruncateCoupledExample.lean",
             LEAN / "CubicPairDeletionConnectivity.lean",
             LEAN / "DualTruncateCyclicSource.lean",
             LEAN / "DualTruncateCyclicSourceExample.lean"]
    return dict(
        status="independent program replay",
        cube_source_vertices=len(graph), cube_source_edges=graph.number_of_edges(),
        cube_vertex_sides_checked=1 << len(graph), cube_nontrivial_sides_checked=len(bounds),
        cube_minimum_nontrivial_boundary=min(bounds), cube_small_cyclic_cuts=cuts,
        cube_pair_deletions_checked=len(pairs), cube_disconnected_pair_deletions=0,
        derived_initial_pair=list(initial[:2]), derived_closing_vertex=initial[2],
        maximum_prior_colours=maximum,
        derived_source_colour_sha256=hashlib.sha256(json.dumps(colours, sort_keys=True).encode()).hexdigest(),
        derived_order_sha256=hashlib.sha256(json.dumps(order).encode()).hexdigest(),
        source_colour_words_read=0,
        diagnostic_vertices=len(diagnostic), diagnostic_deleted_pair=[8, 9],
        diagnostic_pair_deletion_connected=False, diagnostic_small_cyclic_cuts=diagnostic_cuts,
        general_theorem_proved_in_lean=True, cube_cut_interpretation_proved_in_lean=True,
        catalogue_entries_removed=0, global_coverage_proved=False,
        input_sha256={p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in paths},
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "cyclic-source-connectivity-probe.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = json.dumps(run(), indent=2, sort_keys=True) + "\n"
    if args.check:
        assert args.output.read_text() == result, "Cyclic source replay receipt differs."
    else:
        args.output.write_text(result)
    print("Checked all cube cuts and pair deletions, and the cubic separator diagnostic.")


if __name__ == "__main__":
    main()
