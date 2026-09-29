#!/usr/bin/env python3
"""Replay alternating orbits, simple lobes, and their actual facial shores.

These are independent finite program checks, not Lean certificates. The
supplied rotations allow replay without installing or trusting the generator.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
from pathlib import Path

import networkx as nx

from alternating_cycle_probe import alternating_orbits, cycles


def data(rotation):
    rows = [[int(v) for v in row.split(",")] for row in rotation.split(";")]
    assert all(len(row) == len(set(row)) == 3 for row in rows)
    assert all(0 <= v < len(rows) and u != v and u in rows[v]
               for u, row in enumerate(rows) for v in row)
    alpha = {(u, v): (v, u) for u, row in enumerate(rows) for v in row}
    rho = {(u, v): (u, row[(i + 1) % 3])
           for u, row in enumerate(rows) for i, v in enumerate(row)}
    graph = nx.Graph(list(alpha))
    faces = cycles({d: rho[alpha[d]] for d in alpha})
    assert nx.is_connected(graph) and not list(nx.bridges(graph))
    assert len(graph) - graph.number_of_edges() + len(faces) == 2
    assert all(len(f) in (5, 6) and len({d[0] for d in f}) == len(f) for f in faces)
    assert sum(len(f) == 5 for f in faces) == 12
    return graph, alpha, rho, faces


def repeated_vertex(orbit):
    seen = {}
    for i, (dart, _) in enumerate(orbit):
        if dart[0] in seen:
            return {"vertex": dart[0], "positions": [seen[dart[0]], i]}
        seen[dart[0]] = i
    return None


def encode_states(states):
    return ";".join(f"{u},{v},{phase}" for (u, v), phase in states)


def lobe_from(orbit, offset):
    seen, prefix = {}, []
    for i in range(len(orbit) + 1):
        state = orbit[(offset + i) % len(orbit)]
        v = state[0][0]
        if v in seen:
            lobe = prefix[seen[v]:]
            assert 3 <= len(lobe) == len({d[0] for d, _ in lobe})
            assert lobe[-1][0][1] == lobe[0][0][0]
            return lobe
        seen[v] = len(prefix)
        prefix.append(state)
    raise AssertionError("A finite closed orbit must repeat a vertex")


def lobe_shores(graph, alpha, rho, faces, lobe):
    vertices = [d[0] for d, _ in lobe]
    turns = []
    for i, v in enumerate(vertices):
        backward = (v, vertices[(i - 1) % len(vertices)])
        forward = (v, vertices[(i + 1) % len(vertices)])
        assert forward in (rho[backward], rho[rho[backward]])
        turns.append(1 if rho[backward] == forward else -1)
    assert all(turns[i + 1] == -turns[i] for i in range(1, len(turns) - 1))
    assert abs(sum(turns)) <= 2
    for (d, phase), (e, following) in zip(lobe, lobe[1:]):
        assert e == (rho[alpha[d]] if phase == 0 else rho[rho[alpha[d]]])
        assert following == 1 - phase
    cut = {tuple(sorted(d)) for d, _ in lobe}
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    dual = nx.Graph()
    dual.add_nodes_from(range(len(faces)))
    for d in alpha:
        if tuple(sorted(d)) not in cut:
            dual.add_edge(face_of[d], face_of[alpha[d]])
    shores = list(nx.connected_components(dual))
    assert len(shores) == 2
    assert all((tuple(sorted(d)) in cut) ==
               ((face_of[d] in shores[0]) != (face_of[alpha[d]] in shores[0]))
               for d in alpha)
    pentagons = sorted(sum(len(faces[f]) == 5 for f in shore) for shore in shores)
    assert pentagons == [6 - abs(sum(turns)), 6 + abs(sum(turns))]
    return {"vertices": vertices, "dart_phase_segment": encode_states(lobe), "turns": turns,
            "pentagon_shores": pentagons,
            "facial_shores": [sorted(shore) for shore in shores]}


def inspect(example):
    graph, alpha, rho, faces = data(example["rotation"])
    orbits = alternating_orbits(alpha, rho)
    rejected = [dict(orbit=encode_states(orbit), repeat=repeated_vertex(orbit))
                for orbit in orbits if repeated_vertex(orbit) is not None]
    lobes = [lobe_from(orbit, i) for orbit in orbits for i in range(len(orbit))]
    shortest = min(lobes, key=lambda lobe: (len(lobe), lobe))
    return {"id": example["id"], "vertices": len(graph),
            "edges": graph.number_of_edges(),
            "face_lengths": dict(sorted(Counter(map(len, faces)).items())),
            "orbit_lengths": [len(orbit) for orbit in orbits],
            "simple_orbits": len(orbits) - len(rejected),
            "lobes_checked": len(lobes),
            "shortest_lobe": lobe_shores(graph, alpha, rho, faces, shortest),
            "rejected_orbits": rejected if len(rejected) == len(orbits) else []}


def small_cyclic_cuts(graph):
    """Inspect every set of at most four removed edges, not only dual cycles."""
    edges = sorted(graph.edges())
    checked, bad = 0, []
    for count in range(1, 5):
        for indices in combinations(range(len(edges)), count):
            removed = set(indices)
            parent = list(range(len(graph)))

            def find(v):
                while parent[v] != v:
                    parent[v] = parent[parent[v]]
                    v = parent[v]
                return v

            for i, (u, v) in enumerate(edges):
                if i not in removed:
                    parent[find(u)] = find(v)
            vertex_counts = Counter(find(v) for v in graph)
            edge_counts = Counter(find(u) for i, (u, _) in enumerate(edges) if i not in removed)
            if sum(edge_counts[c] >= size for c, size in vertex_counts.items()) >= 2:
                bad.append([edges[i] for i in indices])
            checked += 1
    return {"edge_sets_checked": checked, "cyclic_cuts_of_size_at_most_four": bad}


def tait_colouring(graph):
    edges = sorted(graph.edges())
    incident = {v: [i for i, e in enumerate(edges) if v in e] for v in graph}
    colours = [-1] * len(edges)

    def search():
        choices = []
        for i, (u, v) in enumerate(edges):
            if colours[i] < 0:
                allowed = set(range(3)) - {colours[j] for j in incident[u] + incident[v]}
                if not allowed:
                    return False
                choices.append((len(allowed), i, sorted(allowed)))
        if not choices:
            return True
        _, i, allowed = min(choices)
        for colour in allowed:
            colours[i] = colour
            if search():
                return True
        colours[i] = -1
        return False

    assert search()
    assert all({colours[i] for i in incident[v]} == {0, 1, 2} for v in graph)
    return [[u, v, c] for (u, v), c in zip(edges, colours)]


def run(fixtures):
    source = json.loads(fixtures.read_text())
    results = [inspect(example) for example in source["maps"]]
    failures = [r for r in results if r["simple_orbits"] == 0]
    witness = failures[0]
    raw = next(e for e in source["maps"] if e["id"] == witness["id"])
    graph, _, _, _ = data(raw["rotation"])
    cut_check = small_cyclic_cuts(graph)
    assert not cut_check["cyclic_cuts_of_size_at_most_four"]
    assert witness["vertices"] == 30 and sorted(witness["orbit_lengths"]) == [22, 22, 68, 68]
    assert results[0]["simple_orbits"] == 12
    return {"evidence": "Independent finite program checks, not Lean certificates.",
            "state_encoding": "Semicolon-separated source,target,phase triples.",
            "fixtures_sha256": hashlib.sha256(fixtures.read_bytes()).hexdigest(),
            "maps_checked": len(results), "maps_without_simple_orbits": len(failures),
            "scope": "All dart/phase orbits in the supplied rotations. No minimal-counterexample or reducibility claim.",
            "first_no_simple_orbit": dict(id=witness["id"], **cut_check,
                                          tait_colouring=tait_colouring(graph)),
            "maps": results}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path,
                        default=Path(__file__).with_name("alternating-lobe-fixtures.json"))
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run(args.fixtures)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("maps_checked", "maps_without_simple_orbits")}))
