#!/usr/bin/env python3
"""Replay four-face recognition and isolate the remaining chord obligation.

The fixture census is independent finite evidence. It does not certify
internal-six connectivity or prove universal boundary clearance.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
import hashlib
import itertools
import json
from pathlib import Path

from joint_diamond_occurrence_probe import data, replace, wiring_tables
from mixed_diamond_reduction_probe import HERE, ROOT, CLASSICAL, cycles, read_piece

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def trace(piece, alpha, rho, root):
    """Propagate from the shared edge, independently of the face-length test."""
    image, queue = {32: root}, [32]
    for dart in queue:
        steps = [(piece["rho"][dart], rho[image[dart]])]
        if dart < 34:
            steps.append((piece["alpha"][dart], alpha[image[dart]]))
        for target, actual in steps:
            if target in image:
                assert image[target] == actual
            else:
                image[target] = actual
                queue.append(target)
    assert len(image) == 42
    return image


def chord_obligations(piece):
    """Girth excludes short chords; every remaining chord splits port orbits."""
    vertex, rho, alpha = piece["vertex"], piece["rho"], piece["alpha"]
    adjacency = [set() for _ in range(14)]
    edges = [(vertex[d], vertex[alpha[d]]) for d in range(34) if d < alpha[d]]
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    distance = {}
    for start in range(14):
        queue = deque([(start, 0)])
        while queue:
            vertex_at, length = queue.popleft()
            if (start, vertex_at) in distance:
                continue
            distance[start, vertex_at] = length
            queue.extend((v, length + 1) for v in adjacency[vertex_at])
    ports, rows = vertex[34:], []
    for p, q in itertools.combinations(range(8), 2):
        length = distance[ports[p], ports[q]]
        if length < 4:
            continue
        capped = alpha + list(range(34, 42))
        capped[34 + p], capped[34 + q] = 34 + q, 34 + p
        face_orbits = cycles([rho[capped[d]] for d in range(42)])
        boundary_faces = [sorted(d - 34 for d in face if d >= 34 and d - 34 not in (p, q))
                          for face in face_orbits]
        boundary_faces = sorted(face for face in boundary_faces if face)
        assert len(boundary_faces) == 2
        assert sorted(sum(boundary_faces, [])) == [i for i in range(8) if i not in (p, q)]
        assert all(len(face) >= 2 for face in boundary_faces)
        rows.append({"ports": [p, q], "old_distance": length,
                     "remaining_boundary_orbits": boundary_faces})
    assert len(rows) == 12
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=HERE / "alternating-lobe-fixtures.json")
    parser.add_argument("--output", type=Path, default=HERE / "joint-diamond-face-probe.json")
    args = parser.parse_args()
    piece = read_piece("JointDiamondTangle.lean", 14, 34, 8)
    core_rotation, seam = wiring_tables()
    stats, rows = Counter(), []
    census = hashlib.sha256()
    for raw in json.loads(args.fixtures.read_text())["maps"]:
        graph, alpha, rho, faces = data(raw["rotation"])
        phi = {d: rho[alpha[d]] for d in alpha}
        face_of = {d: i for i, face in enumerate(faces) for d in face}
        found = 0
        stats["maps_checked"] += 1
        for root in alpha:
            stats["rooted_darts_checked"] += 1
            central = [root]
            for _ in range(5):
                central.append(phi[central[-1]])
            selected = [face_of[d] for d in (root, alpha[root], alpha[central[1]], alpha[central[5]])]
            if [len(faces[i]) for i in selected] != [6, 6, 5, 5]:
                continue
            stats["face_patterns"] += 1
            found += 1
            image = trace(piece, alpha, rho, root)
            vertices = {d[0] for d in image.values()}
            face_vertices = {d[0] for i in selected for d in faces[i]}
            assert len(set(selected)) == 4 and vertices == face_vertices
            assert len(vertices) == 14 and len(set(image.values())) == 42
            assert all(image[d][0] == image[e][0] for d in image for e in image
                       if piece["vertex"][d] == piece["vertex"][e])
            ports = [image[i] for i in range(34, 42)]
            assert all(alpha[d][0] not in vertices for d in ports)
            assert graph.subgraph(vertices).number_of_edges() == 17
            stats["boundary_checks_passed"] += 1
            components, properties = replace(graph, alpha, rho, vertices, ports, core_rotation, seam)
            assert len(components) == 1
            assert properties["euler"] == 2 and properties["components"] == 1
            assert properties["bridges"] == properties["self_loops"] == 0
            assert len(graph) == properties["vertices"] + 12
            stats["strict_replacement_checks_passed"] += 1
            census.update((json.dumps([raw["id"], root, sorted(vertices), ports, properties],
                                      sort_keys=True) + "\n").encode())
        rows.append({"id": raw["id"], "vertices": len(graph), "face_patterns": found})
    obligations = chord_obligations(piece)
    paths = [Path(__file__), args.fixtures,
             HERE / "joint_diamond_occurrence_probe.py", HERE / "mixed_diamond_reduction_probe.py",
             HERE / "alternating_lobe_probe.py", HERE / "coupled_wiring_probe.py",
             CLASSICAL / "JointDiamondTangle.lean", CLASSICAL / "DiamondCoupledWiringRotation.lean"]
    report = {
        "status": "independent finite evidence; not universal face-pattern recognition",
        "face_lengths": {"central": 6, "across_root": 6, "neighbours_at_positions_1_and_5": 5},
        "stats": dict(stats), "maps": rows,
        "unverified_domain_property": "Internal-six connectivity of the fixtures is not certified.",
        "remaining_theorem": "Normal form and spherical embedding imply the eight candidate ports leave the fourteen-vertex image.",
        "chord_obligations": obligations,
        "chord_test_scope": "A single extra chord, after vertex injectivity. All twelve candidates not excluded by girth split the remaining ports into two capped-face orbits. Exclusion in an arbitrary ambient map still needs the geometric transport proof.",
        "ordered_census_sha256": census.hexdigest(),
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"stats": stats, "remaining_chord_cases": len(obligations)}, sort_keys=True))


if __name__ == "__main__":
    main()
