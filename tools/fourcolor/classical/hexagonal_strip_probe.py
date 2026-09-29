#!/usr/bin/env python3
"""Check literal strip assembly and fixed-exterior colouring reconstruction.

These are independent finite program checks of selected rotation maps,
separate from the general Lean theorems in HexagonalTubeReduction.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

from hexagonal_seam_probe import cycles, connected


def strip(width, shifts):
    n = len(shifts) + 1
    darts = [(r, t, i, b) for r in range(n) for t in ("a", "b")
             for i in range(width) for b in (0, 1)]
    darts += [(r, t, i, 0) for r in range(n) for t in ("in", "out")
              for i in range(width)]
    darts += [(r, t, i, 0) for r in (-2, -1) for t in ("p", "f", "b")
              for i in range(width)]

    def alpha(d):
        r, t, i, b = d
        if r < 0:
            if t == "p":
                return (0, "in", i, 0) if r == -2 else (n - 1, "out", i, 0)
            return (r, "b", (i + 1) % width, 0) if t == "f" else (
                r, "f", (i - 1) % width, 0)
        if t in ("a", "b"):
            return (r, t, i, 1 - b)
        if t == "in":
            return (-2, "p", i, 0) if r == 0 else (
                r - 1, "out", (i - shifts[r - 1]) % width, 0)
        return (-1, "p", i, 0) if r == n - 1 else (
            r + 1, "in", (i + shifts[r]) % width, 0)

    def rho(d):
        r, t, i, b = d
        if r < 0:
            order = ("p", "b", "f") if r == -2 else ("p", "f", "b")
            return (r, order[(order.index(t) + 1) % 3], i, 0)
        if t == "in":
            return (r, "a", i, 0)
        if t == "out":
            return (r, "a", i, 1)
        if t == "a":
            return (r, "b", (i - 1) % width, 1) if b == 0 else (r, "b", i, 0)
        return (r, "out", i, 0) if b == 0 else (r, "in", (i + 1) % width, 0)

    a, r = {d: alpha(d) for d in darts}, {d: rho(d) for d in darts}
    assert set(a.values()) == set(darts) == set(r.values())
    assert all(a[a[d]] == d and a[d] != d for d in darts)
    vertices, edges = cycles(r), cycles(a)
    vertex_of = {d: i for i, v in enumerate(vertices) for d in v}
    edge_of = {d: i for i, e in enumerate(edges) for d in e}
    endpoints = [tuple(sorted((vertex_of[x], vertex_of[y]))) for x, y in edges]
    faces = cycles({d: r[a[d]] for d in darts})
    assert all(len(v) == 3 for v in vertices)
    assert len(set(endpoints)) == len(edges) and all(x != y for x, y in endpoints)
    assert connected(len(vertices), endpoints)
    assert all(connected(len(vertices), endpoints, e) for e in range(len(edges)))
    assert len(vertices) - len(edges) + len(faces) == 2
    assert Counter(map(len, faces)) == {5: 12, 6: 5 * (n - 1)}
    return a, r, vertices, endpoints, edge_of, faces


def colouring(vertices, edges, fixed):
    c, used = [-1] * len(edges), [set() for _ in range(vertices)]
    for i, colour in sorted(fixed.items()):
        x, y = edges[i]
        assert colour not in used[x] and colour not in used[y]
        c[i] = colour
        used[x].add(colour)
        used[y].add(colour)

    def search():
        free = [i for i, colour in enumerate(c) if colour < 0]
        if not free:
            return True
        options = {i: set(range(3)) - used[edges[i][0]] - used[edges[i][1]] for i in free}
        i = min(free, key=lambda e: (len(options[e]), e))
        x, y = edges[i]
        for colour in sorted(options[i]):
            c[i] = colour
            used[x].add(colour)
            used[y].add(colour)
            if search():
                return True
            used[x].remove(colour)
            used[y].remove(colour)
            c[i] = -1
        return False

    assert search()
    assert all(c[e] == colour for e, colour in fixed.items())
    assert all({c[i] for i, edge in enumerate(edges) if v in edge} == {0, 1, 2}
               for v in range(vertices))
    return c


def example(shifts):
    width, n = 5, len(shifts) + 1
    a, r, vertices, edges, edge_of, faces = strip(width, shifts)
    ca, cr, *_ = strip(width, [0] * (n - 1))
    origins = [0]
    for shift in shifts:
        origins.append((origins[-1] + shift) % width)

    def align(d):
        row, tag, i, bit = d
        offset = 0 if row == -2 else origins[-1] if row == -1 else origins[row]
        return row, tag, (i - offset) % width, bit

    assert set(map(align, a)) == set(ca)
    assert all(align(a[d]) == ca[align(d)] and align(r[d]) == cr[align(d)] for d in a)
    result = {"rows": n, "seam_shifts": shifts, "accumulated_origins": origins,
              "vertices": len(vertices), "edges": len(edges), "faces": len(faces),
              "exact_alpha_rho_relabelling": True, "euler_characteristic": 2,
              "connected_simple_cubic_bridgeless": True}
    if n >= 5:
        _, _, small_vertices, small_edges, small_edge_of, _ = strip(width, [0, 0, origins[-1]])
        small_colours = colouring(len(small_vertices), small_edges, {})
        exterior = [d for d in a if d[0] < 0]
        fixed = {edge_of[d]: small_colours[small_edge_of[d]] for d in exterior}
        restored = colouring(len(vertices), edges, fixed)
        assert all(restored[edge_of[d]] == small_colours[small_edge_of[d]] for d in exterior)
        assert len(vertices) - len(small_vertices) == 10 * (n - 4)
        result.update({"four_ring_vertices": len(small_vertices),
                       "vertices_removed": len(vertices) - len(small_vertices),
                       "exterior_darts_preserved": len(exterior),
                       "exterior_edge_colours_preserved": len(fixed),
                       "original_edge_endpoints": edges, "restored_colours": restored,
                       "four_ring_edge_endpoints": small_edges, "four_ring_colours": small_colours})
    return result


def run():
    return {"evidence": "Independent finite program checks, not Lean certificates.",
            "scope": "Selected capped five-port strips. No universal row-supply claim.",
            "examples": [example(shifts) for shifts in
                         ([0, 0], [2, 4], [0, 0, 0, 0], [2, 4, 1, 3], [4, 2, 3, 1, 4, 2])]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(run(), indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
