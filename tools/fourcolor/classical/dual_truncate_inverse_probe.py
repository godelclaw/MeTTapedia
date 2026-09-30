#!/usr/bin/env python3
"""Recognize actual target rotations through face covers and replay their inverse.

The recognition routine receives only a target rotation. Saved source
rotations and colour words are not inputs. Cube fixture construction is
separate. These program checks are distinct from the uniform Lean inverse
and the kernel-checked cube consumer.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import networkx as nx

from alternating_cycle_probe import cycles
from dual_truncate_geometry_probe import cube_rotation, rotation_data

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def face_cover(graph, faces, face_of):
    vertices = [{d[0] for d in face} for face in faces]
    assert all(len(vs) == len(face) for vs, face in zip(vertices, faces))
    incident = {v: {face_of[v, w] for w in graph[v]} for v in graph}
    assert all(len(fs) == 3 for fs in incident.values())
    mandatory = {i for i, face in enumerate(faces) if len(face) != 6}
    used = set()
    for i in sorted(mandatory):
        if used & vertices[i]:
            return None, 0
        used |= vertices[i]
    nodes = 0

    def search(chosen, covered):
        nonlocal nodes
        nodes += 1
        if len(covered) == len(graph):
            return chosen
        options = [(v, [f for f in incident[v] if not vertices[f] & covered])
                   for v in graph if v not in covered]
        _, options = min(options, key=lambda item: len(item[1]))
        for face in sorted(options):
            result = search(chosen | {face}, covered | vertices[face])
            if result is not None:
                return result
        return None

    return search(mandatory, used), nodes


def recognize(name, raw):
    graph, alpha, rho = rotation_data(raw)
    phi = {d: rho[alpha[d]] for d in alpha}
    faces = cycles(phi)
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    assert nx.is_connected(graph)
    assert all(face_of[d] != face_of[alpha[d]] for d in alpha)
    assert len(graph) - graph.number_of_edges() + len(faces) == 2
    chosen, nodes = face_cover(graph, faces, face_of)
    result = dict(name=name, target_vertices=len(graph), target_faces=len(faces),
                  target_rotation_sha256=hashlib.sha256(raw.encode()).hexdigest(),
                  recognized=chosen is not None, search_nodes=nodes)
    if chosen is None:
        return result
    marked = {v: [d for d in alpha if d[0] == v and face_of[d] in chosen] for v in graph}
    assert all(len(ds) == 1 for ds in marked.values())
    corner = {v: ds[0] for v, ds in marked.items()}
    frame = {(v, i): (rho[corner[v]] if i == 0 else
                      rho[rho[corner[v]]] if i == 1 else corner[v])
             for v in graph for i in range(3)}
    back = {d: x for x, d in frame.items()}
    assert len(back) == len(alpha)
    assert all((face_of[frame[v, i]] in chosen) == (i == 2)
               for v, i in frame)
    a = {v: alpha[frame[v, 0]][0] for v in graph}
    p = {v: alpha[frame[v, 1]][0] for v in graph}
    pinv = {w: v for v, w in p.items()}
    r = {v: p[a[v]] for v in graph}
    assert all(a[a[v]] == v and a[v] != v for v in graph)
    assert len(pinv) == len(graph)
    for v, i in frame:
        recovered_alpha = (a[v], 0) if i == 0 else (p[v], 2) if i == 1 else (pinv[v], 1)
        assert back[alpha[frame[v, i]]] == recovered_alpha
        assert rho[frame[v, i]] == frame[v, (i + 1) % 3]
    source_vertices = cycles(r)
    vertex_of = {v: i for i, vertex in enumerate(source_vertices) for v in vertex}
    assert all(len(vertex) == 3 for vertex in source_vertices)
    assert all(vertex_of[v] != vertex_of[a[v]] for v in graph)
    source_edges = {tuple(sorted((vertex_of[v], vertex_of[a[v]]))) for v in graph}
    assert len(source_edges) == len(graph) // 2  # No parallel source edges in these fixtures.
    source_graph = nx.Graph(list(source_edges))
    assert nx.is_connected(source_graph)
    source_faces = cycles(p)
    assert len(source_vertices) - len(source_edges) + len(source_faces) == 2
    assert sorted(map(len, source_faces)) == sorted(len(faces[i]) for i in chosen)
    result.update(marked_face_ids=sorted(chosen), marked_faces=len(chosen),
                  recovered_source_vertices=len(source_vertices),
                  recovered_source_edges=len(source_edges), recovered_source_faces=len(source_faces),
                  recovered_source_rotation=";".join(
                      ",".join(str(vertex_of[a[v]]) for v in vertex) for vertex in source_vertices),
                  source_euler=2, exact_adapter_darts=len(alpha),
                  source_colour_words_read=0, saved_source_rotations_read=0)
    return result


def cube_target_fixture():
    _, a, r = rotation_data(cube_rotation())
    p = {d: r[a[d]] for d in a}
    inverse = {w: v for v, w in p.items()}
    darts = sorted(a)
    ids = {d: i for i, d in enumerate(darts)}
    return ";".join(",".join(str(ids[e]) for e in (a[d], p[d], inverse[d])) for d in darts)


def run():
    targets_path = HERE / "family-supply-probe.json"
    saved = json.loads(targets_path.read_text())
    targets = {m["id"]: m for m in saved["maps"]}
    results = [recognize("cube", cube_target_fixture())]
    results += [recognize(name, targets[name]["rotation"]) for name in saved["failed_map_ids"]]
    assert all(m["recognized"] for m in results)
    # Nonhexagonal faces must all be marked. Adjacent pentagons in the
    # dodecahedron make such a face-only cover impossible.
    planar, embedding = nx.check_planarity(nx.dodecahedral_graph())
    assert planar
    raw = ";".join(",".join(map(str, embedding.neighbors_cw_order(v))) for v in range(20))
    diagnostic = recognize("dodecahedron", raw)
    assert not diagnostic["recognized"]
    paths = [Path(__file__), targets_path, HERE / "alternating_cycle_probe.py",
             HERE / "dual_truncate_geometry_probe.py", LEAN / "DualTruncateCoupledExample.lean"]
    return dict(status="independent target-only inverse recognition replay", maps=results,
                no_cover_diagnostic=diagnostic, source_colour_words_read=0,
                saved_residual_source_rotations_read=0, uniform_inverse_kernel_proved=True,
                cube_inverse_geometry_and_colouring_kernel_proved=True,
                five_saved_recovered_source_cut_domains_kernel_proved=False,
                catalogue_entries_removed=0, unconditional_tait_to_tait_reduction=False,
                global_coverage_proved=False,
                input_sha256={p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in paths})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "dual-truncate-inverse-probe.json")
    args = parser.parse_args()
    report = run()
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"maps_checked": len(report["maps"]),
                      "exact_adapter_darts": sum(m["exact_adapter_darts"] for m in report["maps"]),
                      "cube_recovered_vertices": report["maps"][0]["recovered_source_vertices"],
                      "dodecahedron_recognized": report["no_cover_diagnostic"]["recognized"]}, indent=2))


if __name__ == "__main__":
    main()
