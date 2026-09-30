#!/usr/bin/env python3
"""Replay literal mixed-diamond replacement geometry outside Lean.

This checks the tables used by the proof, both boundary orientations, edge
identities, and the whole-map vertex count. It is bounded evidence for those
geometric facts, not a colouring-repair proof or a coverage theorem.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CLASSICAL = ROOT / "lean/fourcolor-classical/MettapediaFourColor"

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def cycles(permutation):
    assert sorted(permutation) == list(range(len(permutation)))
    unseen, result = set(range(len(permutation))), []
    while unseen:
        start = dart = min(unseen)
        orbit = []
        while dart in unseen:
            unseen.remove(dart)
            orbit.append(dart)
            dart = permutation[dart]
        assert dart == start
        result.append(orbit)
    return result


def read_piece(name, vertices, internal, ports):
    source = CLASSICAL / name
    text = source.read_text()

    def table(label):
        match = re.search(r"^def " + label + r" : String := (.*)$", text, re.M)
        assert match, label
        return [ord(c) - 65 for c in json.loads(match[1])]

    vertex, rho, inverse = (table(s) for s in ("vertexCodes", "rotationCodes", "inverseCodes"))
    alpha = table("alphaCodes")
    total = internal + ports
    assert len(vertex) == len(rho) == len(inverse) == total
    assert len(alpha) == internal
    assert Counter(vertex) == {i: 3 for i in range(vertices)}
    assert all(inverse[rho[d]] == d == rho[inverse[d]] for d in range(total))
    assert all(vertex[rho[d]] == vertex[d] for d in range(total))
    assert all(len(c) == 3 for c in cycles(rho))
    assert all(alpha[alpha[d]] == d != alpha[d] for d in range(internal))
    assert all(vertex[d] != vertex[alpha[d]] for d in range(internal))
    phi = [rho[alpha[d]] if d < internal else rho[d] for d in range(total)]
    arcs = []
    for i in range(ports):
        dart, arc = phi[internal + i], [internal + i]
        while dart < internal:
            assert dart not in arc
            arc.append(dart)
            dart = phi[dart]
        arc.append(dart)
        assert dart == internal + (i + 1) % ports
        arcs.append(arc)
    faces = len(cycles(phi))
    return {"vertices": vertices, "internal": internal, "ports": ports,
            "vertex": vertex, "rho": rho, "alpha": alpha,
            "first_return_arcs": arcs, "open_faces": faces,
            "euler_mass": 2 * vertices - internal + 2 * faces}


def graph_checks(vertices, edges):
    assert all(a != b for a, b in edges)
    assert Counter(v for edge in edges for v in edge) == {i: 3 for i in range(vertices)}

    def connected_without(omitted):
        adjacency = [set() for _ in range(vertices)]
        for index, (a, b) in enumerate(edges):
            if index != omitted:
                adjacency[a].add(b)
                adjacency[b].add(a)
        reached, queue = {0}, [0]
        for vertex in queue:
            for neighbor in sorted(adjacency[vertex]):
                if neighbor not in reached:
                    reached.add(neighbor)
                    queue.append(neighbor)
        return len(reached) == vertices

    assert connected_without(None)
    # Delete named edges separately, so parallel edges keep their identity.
    assert all(connected_without(i) for i in range(len(edges)))


def sew(left, right, seam):
    assert left["ports"] == right["ports"] == len(seam)
    assert sorted(seam) == list(range(len(seam)))
    offset = len(left["rho"])
    vertex = left["vertex"] + [left["vertices"] + v for v in right["vertex"]]
    rho = left["rho"] + [offset + d for d in right["rho"]]
    alpha = left["alpha"] + [-1] * left["ports"]
    alpha += [offset + d for d in right["alpha"]] + [-1] * right["ports"]
    for port, mate in enumerate(seam):
        a, b = left["internal"] + port, offset + right["internal"] + mate
        alpha[a], alpha[b] = b, a
    assert all(alpha[alpha[d]] == d != alpha[d] for d in range(len(alpha)))
    edges = [(vertex[d], vertex[alpha[d]]) for d in range(len(alpha)) if d < alpha[d]]
    vertices = left["vertices"] + right["vertices"]
    graph_checks(vertices, edges)
    face_count = len(cycles([rho[alpha[d]] for d in range(len(alpha))]))
    return {"vertices": vertices, "edges": len(edges), "faces": face_count,
            "euler": vertices - len(edges) + face_count,
            "connected": True, "bridgeless": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "mixed-diamond-reduction-probe.json")
    args = parser.parse_args()
    old = read_piece("MixedDiamondTangle.lean", 13, 32, 7)
    tree = read_piece("SevenPortTree.lean", 5, 8, 7)
    assert old["open_faces"] == 5 and tree["open_faces"] == 1
    assert old["euler_mass"] == tree["euler_mass"] == 4
    assert set(tree["vertex"][8:]) == set(range(5))
    assert len(set(tree["vertex"][8:])) < 7  # repeated exterior attachments
    times = "".join(chr(65 + len(arc) - 1) for arc in tree["first_return_arcs"])
    assert json.dumps(times) in (CLASSICAL / "SevenPortTree.lean").read_text()
    sewings = []
    for sign in (1, -1):
        for shift in range(7):
            seam = [(sign * i + shift) % 7 for i in range(7)]
            before, after = sew(tree, old, seam), sew(tree, tree, seam)
            assert before["euler"] == after["euler"] == (2 if sign == -1 else -4)
            assert before["vertices"] == after["vertices"] + 8
            sewings.append({"sign": sign, "shift": shift, "before": before, "after": after})
    paths = [Path(__file__), CLASSICAL / "MixedDiamondTangle.lean", CLASSICAL / "SevenPortTree.lean"]
    report = {
        "scope": "Independent bounded geometric replay. Colouring reconstruction and arbitrary-exterior reduction are proved separately in Lean.",
        "interiors": {name: {k: piece[k] for k in ("vertices", "internal", "ports", "first_return_arcs", "open_faces", "euler_mass")}
                      for name, piece in (("mixed_diamond", old), ("replacement", tree))},
        "test_exterior": "The five-vertex seven-port tree, including repeated attachment vertices.",
        "sewings": sewings,
        "summary": {"seam_cases": 14, "planar_cases": 7, "nonplanar_orientation_controls": 7,
                    "whole_map_vertex_decrease": 8},
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report["summary"]))


if __name__ == "__main__":
    main()
