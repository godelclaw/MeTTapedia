#!/usr/bin/env python3
"""Recognize and grow whole hexagonal collars in explicit embedded maps.

These finite program checks are independent evidence, not Lean certificates.
The input to each check is an induced alternating cycle, not a supplied next
row. Counts of maps without such a cycle are retained explicitly.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

import networkx as nx

from hexagonal_seam_probe import cycles
from hexagonal_strip_probe import strip

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from v24_goldberg import make_goldberg_graph


def graph_rotation(edges):
    graph = nx.Graph(edges)
    planar, embedding = nx.check_planarity(graph)
    assert planar and all(graph.degree(v) == 3 for v in graph)
    alpha = {(u, v): (v, u) for u, v in embedding.edges()}
    rho = {}
    for u in embedding:
        neighbours = list(embedding.neighbors_cw_order(u))
        for i, v in enumerate(neighbours):
            rho[u, v] = (u, neighbours[(i + 1) % 3])
    return graph, alpha, rho


def capped_rotation(shifts):
    alpha, rho, vertices, edges, _, _ = strip(5, shifts)
    vertex_of = {d: i for i, star in enumerate(vertices) for d in star}
    convert = {d: (vertex_of[d], vertex_of[alpha[d]]) for d in alpha}
    assert len(set(convert.values())) == len(alpha)
    return nx.Graph(edges), {convert[d]: convert[alpha[d]] for d in alpha}, {
        convert[d]: convert[rho[d]] for d in rho}


def ten_cycles(graph):
    """Every simple ten-cycle once, with the smallest vertex first."""
    found = []

    def visit(path):
        if len(path) == 10:
            if graph.has_edge(path[-1], path[0]) and path[1] < path[-1]:
                found.append(tuple(path))
            return
        for v in sorted(graph[path[-1]]):
            if v > path[0] and v not in path:
                visit(path + [v])

    for start in sorted(graph):
        visit([start])
    return found


def inspect(name, graph, alpha, rho):
    phi = {d: rho[alpha[d]] for d in alpha}
    faces = cycles(phi)
    face_size = {d: len(face) for face in faces for d in face}
    assert all(len(face) in (5, 6) for face in faces)
    assert len(graph) - graph.number_of_edges() + len(faces) == 2
    assert nx.is_connected(graph) and not list(nx.bridges(graph))
    counts = Counter()
    samples, collisions = [], []

    def boundary(side):
        return {d for d in alpha if d[0] in side and d[1] not in side}

    all_cycles = ten_cycles(graph)
    counts["simple_ten_cycles"] = len(all_cycles)
    for cycle in all_cycles:
        for row0 in (cycle, cycle[::-1]):
            third = {u: next(iter(set(graph[u]) - set(row0))) for u in row0
                     if len(set(graph[u]) - set(row0)) == 1}
            if len(third) != 10:
                continue
            incoming = [rho[u, third[u]] == (u, row0[(i + 1) % 10])
                        for i, u in enumerate(row0)]
            if any(incoming[i] == incoming[(i + 1) % 10] for i in range(10)):
                continue
            counts["oriented_induced_alternating_rows"] += 1
            row = row0 if incoming[0] else row0[1:] + row0[:1]
            in_ports = [(row[2 * i], third[row[2 * i]]) for i in range(5)]
            out_ports = [(row[2 * i + 1], third[row[2 * i + 1]]) for i in range(5)]
            remainder = graph.subgraph(set(graph) - set(row))
            inner = set(nx.node_connected_component(remainder, in_ports[0][1]))
            assert boundary(inner) == {alpha[d] for d in in_ports}
            old_side = inner | set(row)
            assert boundary(old_side) == set(out_ports)
            if any(face_size[d] != 6 for d in out_ports):
                counts["pentagonal_seam_obstructions"] += 1
                continue
            counts["all_hexagonal_collars"] += 1
            x = [alpha[d] for d in out_ports]
            y = [alpha[rho[d]] for d in x]
            candidate_vertices = [d[0] for d in x + y]
            if len(set(candidate_vertices)) != 10:
                counts["candidate_vertex_collisions"] += 1
                collisions.append({"row": row, "candidate_vertices": candidate_vertices})
                continue
            assert not (set(candidate_vertices) & old_side)
            a_edges, b_edges = [rho[d] for d in x], [rho[d] for d in y]
            output = [rho[rho[d]] for d in y]
            for i in range(5):
                assert phi[phi[phi[out_ports[i]]]] == x[(i + 1) % 5]
                assert alpha[b_edges[i]] == rho[rho[x[(i + 1) % 5]]]
                assert rho[rho[rho[x[i]]]] == x[i]
                assert rho[rho[rho[y[i]]]] == y[i]
            # All 30 new star darts are present, and every outward edge leaves.
            new_darts = set(x + y + a_edges + b_edges + output +
                            [alpha[d] for d in b_edges])
            assert len(new_darts) == 30
            assert new_darts == {d for d in alpha if d[0] in candidate_vertices}
            new_side = old_side | set(candidate_vertices)
            assert boundary(new_side) == set(output)
            assert all(d[1] not in new_side for d in output)
            next_cycle = [v for i in range(5) for v in (x[i][0], y[i][0])]
            assert all(graph.has_edge(next_cycle[i], next_cycle[(i + 1) % 10])
                       for i in range(10))
            assert graph.subgraph(next_cycle).number_of_edges() == 10
            counts["complete_successor_rows_constructed"] += 1
            if len(samples) < 2:
                samples.append({"row": row, "actual_output_darts": out_ports,
                                "constructed_next_cycle": next_cycle,
                                "new_complete_output_darts": output})
    for key in ("oriented_induced_alternating_rows", "pentagonal_seam_obstructions",
                "all_hexagonal_collars", "candidate_vertex_collisions",
                "complete_successor_rows_constructed"):
        counts.setdefault(key, 0)
    serial = sorted((list(d), list(rho[d])) for d in rho)
    return {"map": name, "vertices": len(graph), "edges": graph.number_of_edges(),
            "face_lengths": dict(sorted(Counter(map(len, faces)).items())),
            "rotation_sha256": hashlib.sha256(json.dumps(serial).encode()).hexdigest(),
            "counts": dict(counts), "sample_constructions": samples,
            "collision_witnesses": collisions}


def run():
    examples = []
    for shifts in ([0, 0], [2, 4], [2, 4, 1, 3], [4, 2, 3, 1, 4, 2]):
        examples.append(inspect(f"capped strip shifts {shifts}", *capped_rotation(shifts)))
    for frequency in (1, 2, 3):
        data = make_goldberg_graph(frequency)
        examples.append(inspect(f"Goldberg GP({frequency},0)",
                                *graph_rotation(data["primal_edges"])))
    return {"evidence": "Independent finite program checks, not Lean certificates.",
            "scope": "All simple ten-cycles in these seven explicit rotations; both orientations tested.",
            "not_established": ["Universal alternating-row supply or a bound on interface width.",
                                "Exclusion or reducibility of collisions in arbitrary planar maps."],
            "examples": examples}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps([{k: e[k] for k in ("map", "vertices", "counts")}
                      for e in result["examples"]], indent=2))
