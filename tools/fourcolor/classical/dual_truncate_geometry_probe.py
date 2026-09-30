#!/usr/bin/env python3
"""Replay exact face identities and geometry of literal expanded rotations.

The cube and five saved residual pairs are checked without colour words.
These finite program checks are separate from the uniform Lean face law
and the kernel-checked cube geometry consumer.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

import networkx as nx

from alternating_cycle_probe import cycles

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def rotation_data(rotation):
    rows = [[int(v) for v in row.split(",")] for row in rotation.split(";")]
    assert all(len(row) == len(set(row)) == 3 for row in rows)
    assert all(0 <= w < len(rows) and w != v and v in rows[w]
               for v, row in enumerate(rows) for w in row)
    alpha = {(v, w): (w, v) for v, row in enumerate(rows) for w in row}
    rho = {(v, w): (v, row[(i + 1) % 3])
           for v, row in enumerate(rows) for i, w in enumerate(row)}
    return nx.Graph(list(alpha)), alpha, rho


def cube_rotation():
    text = (LEAN / "DualTruncateCoupledExample.lean").read_text()
    raw = re.search(r"neighbours\s*:=.*?ByteArray\.mk\s*#\[(.*?)\]", text, re.S)
    assert raw
    flat = bytes(map(int, re.findall(r"\d+", raw.group(1))))
    values = [int.from_bytes(flat[i:i + 2], "little") for i in range(0, len(flat), 2)]
    return ";".join(",".join(map(str, values[i:i + 3])) for i in range(0, len(values), 3))


def analyse(name, rotation, target=None):
    graph, alpha, rho = rotation_data(rotation)
    phi = {d: rho[alpha[d]] for d in alpha}
    inverse = {e: d for d, e in phi.items()}
    faces = cycles(phi)
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    darts = [(d, i) for d in alpha for i in range(3)]
    target_alpha = {(d, i): ((alpha[d], 0) if i == 0 else
                           ((phi[d], 2) if i == 1 else (inverse[d], 1))) for d, i in darts}
    target_phi = {x: (target_alpha[x][0], (target_alpha[x][1] + 1) % 3) for x in darts}
    target_faces = cycles(target_phi)
    tags = {(d, i): (("vertex", d[0]) if i == 0 else
                    (("vertex", alpha[d][0]) if i == 1 else ("face", face_of[d])))
            for d, i in darts}
    assert all(tags[target_phi[x]] == tags[x] for x in darts)
    labels = [tags[face[0]] for face in target_faces]
    assert len(set(labels)) == len(labels) == len(graph) + len(faces)
    assert set(labels) == {("vertex", v) for v in graph} | {("face", i) for i in range(len(faces))}
    assert all(all(tags[x] == tags[face[0]] for x in face) for face in target_faces)
    for face in target_faces:
        kind, index = tags[face[0]]
        assert len(face) == (6 if kind == "vertex" else len(faces[index]))
    assert all(tags[x] != tags[target_alpha[x]] for x in darts)
    expanded = nx.Graph((d, target_alpha[d, i][0]) for d, i in darts)
    assert len(expanded) == len(alpha) == 3 * len(graph)
    assert all(degree == 3 for _, degree in expanded.degree())
    assert nx.is_connected(expanded) and not list(nx.bridges(expanded))
    source_euler = len(graph) - graph.number_of_edges() + len(faces)
    target_euler = len(expanded) - expanded.number_of_edges() + len(target_faces)
    assert source_euler == target_euler == 2
    actual_darts = 0
    if target is not None:
        actual, actual_alpha, actual_rho = rotation_data(target)
        names = sorted({(face_of[d], face_of[alpha[d]]) for d in alpha})
        ids = {pair: i for i, pair in enumerate(names)}
        vertex = {d: ids[face_of[d], face_of[alpha[d]]] for d in alpha}
        assert len(set(vertex.values())) == len(alpha)
        neighbours = {d: (alpha[d], phi[d], inverse[d]) for d in alpha}
        image = lambda x: (vertex[x[0]], vertex[neighbours[x[0]][x[1]]])
        for x in darts:
            assert actual_alpha[image(x)] == image(target_alpha[x])
            assert actual_rho[image(x)] == image((x[0], (x[1] + 1) % 3))
        actual_faces = cycles({d: actual_rho[actual_alpha[d]] for d in actual_alpha})
        assert sorted(map(len, actual_faces)) == sorted(map(len, target_faces))
        assert len(actual) == len(expanded)
        actual_darts = len(darts)
    return dict(name=name, source_vertices=len(graph), source_faces=len(faces),
                target_vertices=len(expanded), target_edges=expanded.number_of_edges(),
                target_faces=len(target_faces), target_vertex_faces=len(graph),
                source_face_lengths=dict(sorted(Counter(map(len, faces)).items())),
                target_face_lengths=dict(sorted(Counter(map(len, target_faces)).items())),
                joint_face_labels_checked=len(darts), actual_target_adapter_darts_checked=actual_darts,
                source_euler=source_euler, target_euler=target_euler,
                target_connected=True, target_bridge_free=True,
                source_geometry_kernel_certified=name == "cube",
                source_rotation_sha256=hashlib.sha256(rotation.encode()).hexdigest())


def run():
    source_path, target_path = HERE / "family-supply-fixtures.json", HERE / "family-supply-probe.json"
    sources = {m["id"]: m for m in json.loads(source_path.read_text())["maps"]}
    saved = json.loads(target_path.read_text())
    targets = {m["id"]: m for m in saved["maps"]}
    results = [analyse("cube", cube_rotation())]
    for target_id in saved["failed_map_ids"]:
        source_id = target_id.removeprefix("dual-truncate-")
        results.append(analyse(source_id, sources[source_id]["rotation"], targets[target_id]["rotation"]))
    # Identity rotations retain the vertices but split each cubic star.
    graph, alpha, _ = rotation_data(cube_rotation())
    split_phi = alpha
    split_faces = cycles(split_phi)
    split_target_phi = {(d, i): ((alpha[d], 1) if i == 0 else
                               ((alpha[d], 0) if i == 1 else (alpha[d], 2)))
                        for d in alpha for i in range(3)}
    split_count = len(cycles(split_target_phi))
    assert split_count != len(graph) + len(split_faces)
    paths = [Path(__file__), source_path, target_path, HERE / "alternating_cycle_probe.py",
             HERE / "hexagonal_seam_probe.py", LEAN / "DualTruncateCoupledExample.lean",
             LEAN / "DualTruncateFaceGeometry.lean", LEAN / "DualTruncateMapGeometry.lean"]
    return dict(status="independent finite geometry replay", maps=results, source_colour_words_read=0,
                split_rotation_diagnostic=dict(source_vertices=len(graph), source_faces=len(split_faces),
                                               target_faces=split_count,
                                               invalid_vertex_plus_source_face_count=len(graph) + len(split_faces)),
                uniform_geometry_proved_in_lean=True, cube_geometry_kernel_certified=True,
                five_saved_source_geometry_domains_kernel_certified=False,
                catalogue_entries_removed=0, global_coverage_proved=False,
                input_sha256={p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in paths})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "dual-truncate-geometry-probe.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = json.dumps(run(), indent=2, sort_keys=True) + "\n"
    if args.check:
        assert args.output.read_text() == result, "Geometry replay receipt differs."
    else:
        args.output.write_text(result)
    print("Checked exact face identities and geometry on the cube and five saved residual maps.")


if __name__ == "__main__":
    main()
