#!/usr/bin/env python3
"""Replay the seven-port mixed diamond's representation and face geometry.

This independently reconstructs the partial diagram, ordered dual and actual
facial occurrences. It does not establish physical Kempe closure of an
arbitrary exterior, strict reduction or universal geometric coverage.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import permutations
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent))
from alternating_cycle_probe import cycles
from alternating_lobe_probe import data
from pentagonal_corona_separation_probe import diagram, shortest_paths, separate
from probe_diamond_joint_repair import literal_graph

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")

OLD_VERTICES = [7, 8, 9, 10, 0, 1, 2, 3, 11, 12, 13, 14, 15]


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def core():
    old_r, old_f, _ = diagram()
    reindex = {v: i for i, v in enumerate(OLD_VERTICES)}
    convert = lambda d: 3 * reindex[d // 3] + d % 3
    r = [convert(old_r[3 * v + s]) for v in OLD_VERTICES for s in range(3)]
    f = {convert(d): convert(e) for d, e in old_f.items()
         if d // 3 in reindex and e // 3 in reindex}
    ports = [d for d in range(39) if d not in f]
    assert ports == [1, 3, 9, 12, 18, 23, 34]
    assert len(f) == 32 and all(f[f[d]] == d for d in f)
    assert all(r[r[r[d]]] == d for d in range(39))
    adjacency = {v: set() for v in range(13)}
    for d, e in f.items():
        adjacency[d // 3].add(e // 3)
    return r, f, ports, adjacency


def codec(r, f, ports):
    alpha = f | {d: 39 + i for i, d in enumerate(ports)} | {39 + i: d for i, d in enumerate(ports)}
    rho = r + list(range(39, 46))
    phi = {d: rho[alpha[d]] for d in range(46)}
    faces = cycles(phi)
    outside = max(faces, key=len)
    assert sorted(map(len, faces)) == [5, 5, 5, 6, 25]
    labels = {d: 7 + i for i, face in enumerate(f for f in faces if f != outside) for d in face}
    for i in range(7):
        d = 39 + i
        while True:
            labels[d] = i
            d = phi[d]
            if d >= 39:
                break
    edges = {tuple(sorted((labels[d], labels[alpha[d]]))) for d in alpha}
    reference = ROOT / "lean/fourcolor-classical/MettapediaFourColor/DiamondConfigurations.lean"
    adjacency, boundary = literal_graph(reference.read_text(), "002")
    target = {(v, w) for v in adjacency for w in adjacency[v] if v < w}
    ring = list(boundary)
    mappings = []
    for shift in range(7):
        for inner in permutations(range(7, 11)):
            mapping = {i: ring[(i + shift) % 7] for i in range(7)} | dict(zip(range(7, 11), inner))
            if {tuple(sorted((mapping[v], mapping[w]))) for v, w in edges} == target:
                mappings.append(mapping)
    assert len(mappings) == 1
    mapping = mappings[0]
    ordered = [next(d for d in ports if mapping[labels[d]] == v) for v in ring]
    assert [(mapping[labels[d]], mapping[labels[alpha[d]]]) for d in ordered] == [
        (ring[i], ring[(i + 1) % 7]) for i in range(7)]
    darts = sorted(f) + ordered
    inverse = {d: i for i, d in enumerate(darts)}
    code = lambda xs: "".join(chr(65 + x) for x in xs)
    tables = {
        "vertexCodes": code([d // 3 for d in darts]),
        "rotationCodes": code([inverse[r[d]] for d in darts]),
        "inverseCodes": code([inverse[r[r[d]]] for d in darts]),
        "leftCodes": code([mapping[labels[d]] for d in darts]),
        "rightCodes": code([mapping[labels[alpha[d]]] for d in darts]),
        "alphaCodes": code([inverse[f[d]] for d in darts[:32]]),
    }
    source = ROOT / "lean/fourcolor-classical/MettapediaFourColor/MixedDiamondTangle.lean"
    text = source.read_text()
    for name, expected in tables.items():
        match = re.search(r"def " + name + r" : String := (.*)", text)
        assert match and json.loads(match[1]) == expected, name
    separation = ROOT / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/MixedDiamondSeparation.lean"
    flip_text = re.search(r"def flipCodes : String := (.*)", separation.read_text())
    assert json.loads(flip_text[1]) == "".join(chr(65 + f[d]) if d in f else "@" for d in range(39))
    recognition = ROOT / "lean/fourcolor-classical/MettapediaFourColor/MixedDiamondRecognition.lean"
    coordinate = recognition.read_text().split("def coordinate", 1)[1].split("theorem coordinate_vertex", 1)[0]
    strings = re.findall(r'lookup ("(?:[^"\\]|\\.)*")', coordinate)
    assert list(map(json.loads, strings)) == [code(darts), code([inverse[d] for d in range(39)])]
    return {"dual_vertex_map": [mapping[i] for i in range(11)], "ordered_reference_boundary": ring,
            "ordered_ports": ordered, "literal_vertices": 13, "internal_edges": 16,
            "ports": 7, "bounded_face_lengths": [5, 5, 5, 6],
            "checked_tables": sorted(tables) + ["flipCodes", "coordinate", "coordinate_inverse"],
            "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in (reference, source, separation, recognition)}}


def separation(r, f, adjacency):
    paths = shortest_paths(adjacency)
    records, missed = [], []
    for u in range(13):
        for v in range(13):
            if u == v:
                continue
            for s in range(3):
                t = separate(3 * u, 3 * v + s, 3, r, f, paths)
                if t is None:
                    missed.append([u, v, s])
                    t = separate(3 * u, 3 * v + s, 4, r, f, paths)
                assert t is not None
                x, y = 3 * u, 3 * v + s
                for op in t["word"]:
                    if op == "r":
                        x, y = r[x], r[y]
                    else:
                        assert op == "a" and x in f and y in f
                        x, y = f[x], f[y]
                assert [x, y] == t["target_darts"] and x != y
                p = t["vertex_path"]
                assert (p[0], p[-1]) == (x // 3, y // 3)
                assert all(b in adjacency[a] for a, b in zip(p, p[1:]))
                assert len(set(p)) == len(p) and len(p) <= 5
                records.append({"source": [u, v, s], **t})
    assert missed == [[0, 7, 2], [1, 6, 1], [6, 1, 2], [7, 0, 1]]
    return {"cases": len(records), "triangle_free_unresolved": missed,
            "four_cycle_paths": [x for x in records if x["source"] in missed],
            "transport_length_histogram": dict(sorted(Counter(len(x["word"]) for x in records).items())),
            "all_traces_sha256": digest(records)}


def scan(raw, r, f, ports):
    _, alpha, rho, faces = data(raw["rotation"])
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    found = []
    for face in faces:
        if len(face) != 5:
            continue
        for offset in range(5):
            center = face[offset:] + face[:offset]
            lengths = [len(faces[face_of[alpha[d]]]) for d in center]
            if [lengths[i] for i in (4, 0, 1)] != [5, 6, 5]:
                continue
            incoming = [alpha[rho[d]] for d in center]
            first = [rho[d] for d in incoming]
            bases = [alpha[first[0]], incoming[0], alpha[first[4]], incoming[4],
                     alpha[first[3]], incoming[3], alpha[first[2]], incoming[2],
                     alpha[first[1]], incoming[1], alpha[rho[alpha[first[0]]]]]
            actual = []
            for old in OLD_VERTICES[:8]:
                b = bases[old]
                actual.extend([rho[rho[b]], rho[b], b] if old % 2 == 0 else [b, rho[b], rho[rho[b]]])
            for d in center:
                actual.extend([d, rho[d], rho[rho[d]]])
            vertices = [actual[3 * i][0] for i in range(13)]
            assert len(set(vertices)) == 13
            assert all(rho[actual[d]] == actual[r[d]] for d in range(39))
            assert all(alpha[actual[d]] == actual[e] for d, e in f.items())
            outgoing = [d for d in ports if actual[d][1] not in vertices]
            assert sum(v in vertices and w not in vertices for v, w in alpha) == len(outgoing)
            found.append({"id": raw["id"], "central_face": face_of[center[0]],
                          "root": list(center[0]), "vertices": vertices,
                          "neighbour_lengths": lengths, "actual_ports": len(outgoing)})
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=HERE / "alternating-lobe-fixtures.json")
    parser.add_argument("--output", type=Path, default=HERE / "mixed-diamond-probe.json")
    args = parser.parse_args()
    r, f, ports, adjacency = core()
    codec_report = codec(r, f, ports)
    separation_report = separation(r, f, adjacency)
    fixtures = json.loads(args.fixtures.read_text())["maps"]
    found = [hit for raw in fixtures for hit in scan(raw, r, f, ports)]
    report = {
        "scope": "Independent program evidence for the literal representation and existing fixtures. Normal-form hypotheses, physical exterior closure, strict reduction and universal coverage are not inferred from the census.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "fixtures_sha256": hashlib.sha256(args.fixtures.read_bytes()).hexdigest(),
        "literal_codec": codec_report, "separation": separation_report,
        "face_census": {"maps": len(fixtures), "rooted_occurrences": len(found),
                        "distinct_central_faces": len({(x["id"], x["central_face"]) for x in found}),
                        "distinct_vertex_subsets": len({(x["id"], tuple(sorted(x["vertices"]))) for x in found}),
                        "maps_with_pattern": len({x["id"] for x in found}),
                        "actual_port_histogram": dict(sorted(Counter(x["actual_ports"] for x in found).items())),
                        "all_occurrences_sha256": digest(found),
                        "first_occurrence": next(iter(found), None)},
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"separation_cases": separation_report["cases"],
                      "face_census": report["face_census"]}, indent=2))


if __name__ == "__main__":
    main()
