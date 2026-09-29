#!/usr/bin/env python3
"""Independently inspect seam faces in literal oriented cubic rows.

This finite experiment uses dart permutations, not the Lean three-step
proof. It is evidence about concrete examples; the general alignment and
colouring theorems are in HexagonalSlabSeam and HexagonalTubeChain.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import permutations
import json
from pathlib import Path


def cycles(perm):
    unseen = set(perm)
    result = []
    while unseen:
        start = min(unseen)
        orbit, current = [], start
        while current not in orbit:
            orbit.append(current)
            unseen.remove(current)
            current = perm[current]
        assert current == start
        result.append(orbit)
    return result


def rows(width, seam, capped=False):
    assert sorted(seam) == list(range(width))
    inverse = {j: i for i, j in enumerate(seam)}
    darts = [(r, t, i, b) for r in range(2) for t in ("a", "b")
             for i in range(width) for b in (0, 1)]
    darts += [(r, t, i, 0) for r in range(2) for t in ("in", "out")
              for i in range(width)]
    if capped:
        darts += [(r, t, i, 0) for r in (2, 3) for t in ("p", "f", "b")
                  for i in range(width)]

    def alpha(d):
        r, t, i, b = d
        if r >= 2:
            if t == "p":
                return (r - 2, "in" if r == 2 else "out", i, 0)
            return (r, "b", (i + 1) % width, 0) if t == "f" else (
                r, "f", (i - 1) % width, 0)
        if t in ("a", "b"):
            return (r, t, i, 1 - b)
        if r == 0 and t == "out":
            return (1, "in", seam[i], 0)
        if r == 1 and t == "in":
            return (0, "out", inverse[i], 0)
        return (r + 2, "p", i, 0) if capped else d

    def rho(d):
        r, t, i, b = d
        if r >= 2:
            order = ("p", "b", "f") if r == 2 else ("p", "f", "b")
            return (r, order[(order.index(t) + 1) % 3], i, 0)
        if t == "in":
            return (r, "a", i, 0)
        if t == "out":
            return (r, "a", i, 1)
        if t == "a" and b == 0:
            return (r, "b", (i - 1) % width, 1)
        if t == "a" and b == 1:
            return (r, "b", i, 0)
        if t == "b" and b == 0:
            return (r, "out", i, 0)
        return (r, "in", (i + 1) % width, 0)

    alpha_map = {d: alpha(d) for d in darts}
    rho_map = {d: rho(d) for d in darts}
    phi = {d: rho(alpha(d)) for d in darts}
    assert all(alpha(alpha(d)) == d for d in darts)
    assert len(set(rho_map.values())) == len(darts)
    assert len(set(phi.values())) == len(darts)
    faces = cycles(phi)
    face_size = {d: len(face) for face in faces for d in face}
    seam_lengths = [face_size[(0, "out", i, 0)] for i in range(width)]
    return alpha_map, rho_map, faces, seam_lengths


def connected(vertex_count, edges, omit=None):
    reached, todo = {0}, [0]
    while todo:
        v = todo.pop()
        for index, (a, b) in enumerate(edges):
            if index == omit or v not in (a, b):
                continue
            w = b if a == v else a
            if w not in reached:
                reached.add(w)
                todo.append(w)
    return len(reached) == vertex_count


def tait_colouring(vertex_count, edges):
    colours = [-1] * len(edges)
    used = [set() for _ in range(vertex_count)]

    def search():
        uncoloured = [i for i, c in enumerate(colours) if c < 0]
        if not uncoloured:
            return True
        options = {i: set(range(3)) - used[edges[i][0]] - used[edges[i][1]]
                   for i in uncoloured}
        i = min(uncoloured, key=lambda e: (len(options[e]), e))
        a, b = edges[i]
        for c in sorted(options[i]):
            colours[i] = c
            used[a].add(c)
            used[b].add(c)
            if search():
                return True
            used[a].remove(c)
            used[b].remove(c)
            colours[i] = -1
        return False

    assert search()
    assert all({colours[i] for i, e in enumerate(edges) if v in e} == {0, 1, 2}
               for v in range(vertex_count))
    return colours


def closed_example(seam):
    alpha, rho, faces, seam_lengths = rows(5, seam, capped=True)
    vertices = cycles(rho)
    vertex_of = {d: i for i, vertex in enumerate(vertices) for d in vertex}
    edge_darts = cycles(alpha)
    assert all(len(v) == 3 for v in vertices)
    assert all(len(e) == 2 for e in edge_darts)
    edges = [tuple(sorted((vertex_of[a], vertex_of[b]))) for a, b in edge_darts]
    assert len(set(edges)) == len(edges) and all(a != b for a, b in edges)
    assert connected(len(vertices), edges)
    assert all(connected(len(vertices), edges, i) for i in range(len(edges)))
    return {"seam": list(seam), "vertices": len(vertices), "edges": len(edges),
            "faces": len(faces), "euler_characteristic": len(vertices)-len(edges)+len(faces),
            "face_length_counts": dict(sorted(Counter(map(len, faces)).items())),
            "seam_face_lengths": seam_lengths, "connected_simple_cubic_bridgeless": True,
            "edge_endpoints": edges, "tait_colours": tait_colouring(len(vertices), edges)}


def run(max_width):
    tests = []
    for width in range(2, max_width + 1):
        total = hexagonal = 0
        first_failure = None
        for seam in permutations(range(width)):
            *_, lengths = rows(width, seam)
            all_hex = all(n == 6 for n in lengths)
            cyclic = all(seam[i] == (i + seam[0]) % width for i in range(width))
            assert all_hex == cyclic, (width, seam, lengths)
            assert all(n % 6 == 0 for n in lengths)
            if not all_hex and first_failure is None:
                first_failure = {"seam": list(seam), "seam_face_lengths": lengths}
            total += 1
            hexagonal += all_hex
        tests.append({"width": width, "matchings_checked": total,
                      "hexagonal_matchings": hexagonal, "translations": width,
                      "first_nontranslation": first_failure})
    examples = [closed_example(p) for p in [(0, 1, 2, 3, 4), (2, 3, 4, 0, 1), (0, 1, 2, 4, 3)]]
    assert [e["euler_characteristic"] for e in examples] == [2, 2, 0]
    assert all(examples[i]["face_length_counts"] == {5: 12, 6: 5} for i in (0, 1))
    return {"evidence": "Independent finite program checks, not Lean certificates.",
            "claim": "In two literal oriented rows, every seam face is hexagonal iff the seam is a cyclic translation.",
            "rows": tests, "closed_five_port_examples": examples,
            "scope": "The nontranslation control is a toroidal rotation system. No nontranslation spherical example or universal row-supply claim is made."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=7)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.max_width < 2:
        parser.error("max-width must be at least 2")
    text = json.dumps(run(args.max_width), indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
