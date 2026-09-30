#!/usr/bin/env python3
"""Replay the coupled wiring at literal occurrences in saved fullerene maps.

Recognize all darts, rotations, internal edges and outgoing ports of the
fourteen-vertex piece. Check the rewired map with named edge identities.
These are independent finite checks, not a proof of universal recognition
or a certification of internal-six connectivity of the fixture collection.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

import networkx as nx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from alternating_lobe_probe import data
from coupled_wiring_probe import graph_properties
from mixed_diamond_reduction_probe import CLASSICAL, ROOT, read_piece

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def recognize(piece, alpha, rho, root):
    """Propagate every specified generator; accept only complete embeddings."""
    image, queue = {0: root}, [0]
    for dart in queue:
        steps = [(piece["rho"][dart], rho[image[dart]])]
        if dart < 34:
            steps.append((piece["alpha"][dart], alpha[image[dart]]))
        for target, actual in steps:
            if target in image:
                if image[target] != actual:
                    return None
            else:
                image[target] = actual
                queue.append(target)
    assert len(image) == 42
    vertices = {image[d][0] for d in image}
    if len(vertices) != 14:
        return None
    assert len(set(image.values())) == 42
    assert all(image[d][0] == image[e][0]
               for d in image for e in image if piece["vertex"][d] == piece["vertex"][e])
    ports = [image[d] for d in range(34, 42)]
    if any(alpha[d][0] in vertices for d in ports):
        return None
    assert all(image[piece["rho"][d]] == rho[image[d]] for d in image)
    assert all(image[piece["alpha"][d]] == alpha[image[d]] for d in range(34))
    return vertices, ports


def wiring_tables():
    source = (CLASSICAL / "DiamondCoupledWiringRotation.lean").read_text()
    rotation = json.loads(re.search(
        r'def coreRotation[^\n]*\n  toFun := !(\[[^\]]*\])', source)[1])
    block = source.split("def seamFun")[1].split("def seam :")[0]
    seam = [int(i) + (0 if tag == "inl" else 8)
            for tag, i in re.findall(r'\.(inl|inr) (\d+)', block)]
    assert len(rotation) == 6 and len(seam) == 14
    assert all(seam[seam[i]] == i != seam[i] for i in range(14))
    return rotation, seam


def replace(graph, alpha, rho, vertices, ports, core_rotation, seam):
    outside = set(graph) - vertices
    components = list(nx.connected_components(graph.subgraph(outside)))
    darts = [d for d in alpha if d[0] in outside]
    index = {d: i for i, d in enumerate(darts)}
    vertex_index = {v: i for i, v in enumerate(sorted(outside))}
    count, offset = len(outside), len(darts)
    new_vertices = [vertex_index[d[0]] for d in darts] + [count] * 3 + [count + 1] * 3
    rotation = [index[rho[d]] for d in darts] + [offset + i for i in core_rotation]
    edges = [index.get(alpha[d], -1) for d in darts] + [-1] * 6
    boundary = [index[alpha[d]] for d in ports] + list(range(offset, offset + 6))
    for i, j in enumerate(seam):
        edges[boundary[i]] = boundary[j]
    properties = graph_properties(new_vertices, rotation, edges)
    assert len(graph) - properties["vertices"] == 12
    return components, properties


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=HERE / "alternating-lobe-fixtures.json")
    parser.add_argument("--output", type=Path, default=HERE / "joint-diamond-occurrence-probe.json")
    args = parser.parse_args()
    piece = read_piece("JointDiamondTangle.lean", 14, 34, 8)
    core_rotation, seam = wiring_tables()
    stats, sizes, rows, examples = Counter(), Counter(), [], []
    census = hashlib.sha256()
    for raw in json.loads(args.fixtures.read_text())["maps"]:
        graph, alpha, rho, _ = data(raw["rotation"])
        stats["maps_checked"] += 1
        found, vertex_sets = 0, set()
        for root in alpha:
            stats["rooted_darts_checked"] += 1
            occurrence = recognize(piece, alpha, rho, root)
            if occurrence is None:
                continue
            vertices, ports = occurrence
            found += 1
            vertex_sets.add(tuple(sorted(vertices)))
            stats["occurrences"] += 1
            sizes[len(graph)] += 1
            components, properties = replace(graph, alpha, rho, vertices, ports, core_rotation, seam)
            stats[f"exterior_components_{len(components)}"] += 1
            stats[f"replacement_minimum_face_{properties['minimum_face_length']}"] += 1
            assert len(components) == 1, (raw["id"], root, components)
            assert properties["euler"] == 2 and properties["components"] == 1, (raw["id"], root)
            assert properties["bridges"] == properties["self_loops"] == 0, (raw["id"], root)
            witness = {"id": raw["id"], "root": root, "core_vertices": sorted(vertices),
                       "ports": ports, "outside_components": sorted(map(len, components)),
                       "wired": properties}
            census.update((json.dumps(witness, sort_keys=True) + "\n").encode())
            if len(examples) < 4:
                examples.append(witness)
        if found:
            stats["maps_with_occurrence"] += 1
        stats["distinct_vertex_subsets"] += len(vertex_sets)
        rows.append({"id": raw["id"], "vertices": len(graph),
                     "occurrences": found, "vertex_subsets": len(vertex_sets)})
    paths = [Path(__file__), args.fixtures, HERE / "alternating_lobe_probe.py",
             HERE / "coupled_wiring_probe.py", HERE / "mixed_diamond_reduction_probe.py",
             CLASSICAL / "JointDiamondTangle.lean", CLASSICAL / "DiamondCoupledWiringRotation.lean"]
    result = {
        "status": "independent finite evidence; not a universal replacement theorem",
        "checked_source_domain": "Connected simple cubic spherical rotations with simple pentagonal or hexagonal faces and no bridges; exactly twelve pentagons.",
        "unverified_domain_property": "Internal-six connectivity is not certified by this census.",
        "stats": dict(stats), "occurrences_by_ambient_vertices": dict(sorted(sizes.items())),
        "whole_map_vertex_difference": 12, "ordered_census_sha256": census.hexdigest(),
        "maps": rows, "examples": examples,
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in paths}}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"{stats['occurrences']} rooted occurrences in {stats['maps_with_occurrence']} of "
          f"{stats['maps_checked']} maps; every exterior connected; every wiring planar, "
          "connected and bridgeless; net twelve vertices removed.")


if __name__ == "__main__":
    main()
