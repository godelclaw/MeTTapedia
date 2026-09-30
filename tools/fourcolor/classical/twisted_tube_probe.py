#!/usr/bin/env python3
"""Replay complementary-ring reconstruction and actual sparse-map reductions.

Finite program evidence, separate from the general Lean reduction theorem.
Every original exterior edge colour is retained. The replacement changes the
right seam by one cyclic port and removes exactly two complete rows.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

import networkx as nx

from alternating_cycle_probe import alternating_orbits, oriented_row, grow, cycles
from alternating_lobe_probe import data, tait_colouring

HERE = Path(__file__).resolve().parent

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def ring_colours(a, b):
    k = len(a)
    x = tuple(a[i] ^ b[(i - 1) % k] for i in range(k))
    y = tuple(a[i] ^ b[i] for i in range(k))
    assert all(c in (1, 2, 3) for c in (*a, *b, *x, *y))
    assert all(len({x[i], a[i], b[(i - 1) % k]}) == 3 for i in range(k))
    assert all(len({y[i], a[i], b[i]}) == 3 for i in range(k))
    return x, y


def complementary(a, b):
    """The original, complementary, and shifted original ring witnesses."""
    shift = lambda w: w[1:] + w[:1]
    x, y = ring_colours(a, b)
    middle = b, shift(a)
    last = shift(a), shift(b)
    assert ring_colours(*middle) == (y, shift(x))
    assert ring_colours(*last) == (shift(x), shift(y))
    return middle, last


def exhaustive(width):
    count = 0

    def visit(es):
        nonlocal count
        if len(es) == 2 * width:
            if es[-1] == es[0]:
                return
            complementary(tuple(es[::2]), tuple(es[1::2]))
            count += 1
            return
        for c in (1, 2, 3):
            if c != es[-1]:
                visit(es + [c])

    for c in (1, 2, 3):
        visit([c])
    assert count == 2 ** (2 * width) + 2
    return {"width": width, "ring_colourings": count, "all_reconstructions_valid": True}


def reduce_example(raw):
    graph, alpha, rho, faces = data(raw["rotation"])
    face_of = {d: face for face in faces for d in face}
    histories = []
    for orbit in alternating_orbits(alpha, rho):
        row = oriented_row(graph, rho, orbit)
        if row is not None:
            histories.append(grow(graph, alpha, rho, face_of, row))
    history = max(histories, key=lambda h: h["successful_extensions"])
    rows = list(map(tuple, history["rows"]))
    if len(rows) < 3:
        return {"map": raw["id"], "vertices": len(graph), "rows": len(rows),
                "width": history["width"], "eligible": False}
    width = history["width"]
    retained, deleted = rows[:-2], set(rows[-2] + rows[-1])
    row = retained[-1]
    outputs = [next(v for v in graph[rows[-1][2*i+1]] if v not in rows[-1])
               for i in range(width)]
    redirects = {}
    for i in range(width):
        u, v = row[2*((i+1) % width)+1], outputs[i]
        redirects[u, rows[-2][2*((i+1) % width)]] = v
        redirects[v, rows[-1][2*i+1]] = u
    assert len(redirects) == 2 * width
    small_rotation = {}
    for u in graph:
        if u in deleted:
            continue
        # Retain the actual cyclic star, changing only consumed seam mates.
        start = min(graph[u])
        star = [start, rho[u, start][1], rho[rho[u, start]][1]]
        small_rotation[u] = [redirects.get((u, v), v) for v in star]
        assert not deleted.intersection(small_rotation[u])
    small = nx.Graph()
    small_rho = {}
    for u, star in small_rotation.items():
        assert len(set(star)) == 3 and u not in star
        for j, v in enumerate(star):
            assert u in small_rotation[v]
            small.add_edge(u, v)
            small_rho[u, v] = (u, star[(j+1) % 3])
    small_faces = cycles({d: small_rho[d[::-1]] for d in small_rho})
    assert nx.is_connected(small) and not list(nx.bridges(small))
    assert len(small) - small.number_of_edges() + len(small_faces) == 2
    assert len(graph) - len(small) == 4 * width
    coloured = tait_colouring(small)
    small_c = {frozenset((u, v)): c+1 for u, v, c in coloured}
    colour = lambda u, v: small_c[frozenset((u, v))]
    a = tuple(colour(row[2*i], row[2*i+1]) for i in range(width))
    b = tuple(colour(row[2*i+1], row[(2*i+2) % (2*width)]) for i in range(width))
    x, y = ring_colours(a, b)
    new_rings = complementary(a, b)
    restored = {e: c for e, c in small_c.items() if all(v not in set(row) for v in e)}
    # Retained old edges, including all earlier rows, keep their colours.
    for u, v in graph.edges():
        if u not in deleted and v not in deleted and frozenset((u, v)) in small_c:
            restored[frozenset((u, v))] = colour(u, v)
    for i in range(width):
        restored[frozenset((row[2*i+1], rows[-2][2*i]))] = y[i]
    for j, (aa, bb) in enumerate(new_rings):
        rr = rows[-2+j]
        xx, yy = ring_colours(aa, bb)
        for i in range(width):
            restored[frozenset((rr[2*i], rr[2*i+1]))] = aa[i]
            restored[frozenset((rr[2*i+1], rr[(2*i+2) % (2*width)]))] = bb[i]
            nxt = rows[-1][2*i] if j == 0 else outputs[i]
            restored[frozenset((rr[2*i+1], nxt))] = yy[i]
    actual_edges = {frozenset(e) for e in graph.edges()}
    restored = {e: c for e, c in restored.items() if e in actual_edges}
    assert set(restored) == actual_edges
    assert all({restored[frozenset((u, v))] for v in graph[u]} == {1, 2, 3} for u in graph)
    tube_vertices = set().union(*map(set, rows))
    exterior = {d for d in alpha if d[0] not in tube_vertices}
    for u, v in exterior:
        sv = redirects.get((u, v), v)
        assert restored[frozenset((u, v))] == colour(u, sv)
    return {"map": raw["id"], "vertices": len(graph), "rows": len(rows),
            "width": width, "eligible": True, "shortened_vertices": len(small),
            "retained_rows": len(retained), "vertices_removed": 4*width,
            "source_rows": rows, "new_output_neighbours": outputs,
            "small_rotation": small_rotation,
            "small_face_lengths": dict(sorted(Counter(map(len, small_faces)).items())),
            "small_colour_edges": coloured,
            "restored_colour_edges": [[*sorted(e), c] for e, c in
                                      sorted(restored.items(), key=lambda ec: sorted(ec[0]))],
            "exterior_darts_preserved": len(exterior),
            "euler": 2, "connected_cubic_bridgeless": True,
            "rotation_sha256": hashlib.sha256(raw["rotation"].encode()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=HERE / "diamond-supply-probe.json")
    parser.add_argument("--output", type=Path, default=HERE / "twisted-tube-probe.json")
    args = parser.parse_args()
    if args.output.resolve() in {args.input.resolve(), Path(__file__).resolve()}:
        parser.error("The output must not overwrite the program or input.")
    controls = json.loads(args.input.read_text())["controls"]
    report = {"evidence": "Independent finite program checks, not Lean certificates.",
              "input_sha256": hashlib.sha256(args.input.read_bytes()).hexdigest(),
              "program_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "algebra": [exhaustive(k) for k in range(2, 9)],
              "physical": [reduce_example(raw) for raw in controls]}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"ring_colourings": sum(r["ring_colourings"] for r in report["algebra"]),
                      "physical": [{key: row[key] for key in
                                    ("map", "vertices", "rows", "width", "eligible")}
                                   for row in report["physical"]]}))


if __name__ == "__main__":
    main()
