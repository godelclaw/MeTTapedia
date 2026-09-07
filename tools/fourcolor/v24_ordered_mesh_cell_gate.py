#!/usr/bin/env python3
"""Preregistered ordered-mesh cell-boundary construction test.

Four branch-to-branch paths are a candidate disk rim. Reject non-simple
closed walks and record whether any designated corner has degree one in
their union (then no simple cycle in that union can retain the corner).
Controls use the existing full spherical GP receipts and a pentagonal
facial cycle; no colourings or counterexample-class assumptions are used.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_contour_mesh_gate import verify_archive
from v24_geodesic_mincut_gate import connected


def segment(path, start, stop):
    i, j = path.index(start), path.index(stop)
    return path[i:j + 1] if i <= j else list(reversed(path[j:i + 1]))


def inspect(rows, cols, edges):
    branch = [[next(v for v in col if v in row) for col in cols] for row in rows]
    assert len(set(sum(branch, []))) == 4
    assert all(len(path) == len(set(path)) for path in rows + cols)
    assert set(rows[0]).isdisjoint(rows[1]) and set(cols[0]).isdisjoint(cols[1])
    assert all(row.index(bs[0]) < row.index(bs[1]) for row, bs in zip(rows, branch))
    assert all(col.index(branch[0][j]) < col.index(branch[1][j]) for j, col in enumerate(cols))
    rim = [segment(rows[0], branch[0][0], branch[0][1]),
           segment(cols[1], branch[0][1], branch[1][1]),
           segment(rows[1], branch[1][1], branch[1][0]),
           segment(cols[0], branch[1][0], branch[0][0])]
    walk = sum([part[:-1] for part in rim], [])
    edge_set = {tuple(sorted(e)) for e in edges}
    union = {tuple(sorted(e)) for e in zip(walk, walk[1:] + walk[:1])}
    assert union <= edge_set and len(walk) >= 4
    degree = {v: sum(v in e for e in union) for v in set(walk)}
    corners = sum(branch, [])
    side = set(walk)
    vertices = {v for edge in edges for v in edge}
    n = max(vertices) + 1
    assert vertices == set(range(n))
    inner_edges = [e for e in edges if set(e) <= side]
    outer_edges = [e for e in edges if set(e).isdisjoint(side)]
    return dict(rows=rows, columns=cols, branches=branch, rim_paths=rim,
                walk=walk, simple=len(walk) == len(set(walk)),
                union_edges=sorted(union),
                pendant_corners=[v for v in corners if degree[v] == 1],
                complete_vertex_boundary=sum((u in side) != (v in side) for u, v in edges),
                side_connected=connected(n, edges, side),
                complement_connected=connected(n, edges, vertices - side),
                side_edges=len(inner_edges), complement_edges=len(outer_edges),
                side_vertices=len(side), complement_vertices=len(vertices - side),
                inside_majority_failures=[v for v in sorted(side)
                                          if sum(v in e for e in inner_edges) < 2])


def audit(archive, ordered):
    verify_archive(archive)
    assert len(archive["receipts"]) == len(ordered["spheres"]) == 8
    first = archive["receipts"][0]["graph"]
    face = first["face_cycles"][0]
    assert len(face) == 5
    positive = inspect([[face[0], face[1]], [face[3], face[2]]],
                       [[face[0], face[4], face[3]], [face[1], face[2]]], first["primal_edges"])
    assert positive["simple"] and not positive["pendant_corners"]
    summaries, witness = [], None
    for receipt, order in zip(archive["receipts"], ordered["spheres"]):
        assert receipt["frequency"] == order["frequency"]
        lo, hi = receipt["selected"]
        assert len(order["row_directions"]) == hi - lo + 1
        assert len(order["selected_columns"]) == len(set(order["selected_columns"]))
        rows = [r["cycle"] if d else r["cycle"][::-1]
                for r, d in zip(receipt["contours"][lo:hi + 1], order["row_directions"])]
        cols = [receipt["paths"][j] for j in order["selected_columns"]]
        assert len(rows) >= 2 and len(cols) >= 2
        count = bad = pendant = 0
        for i, j in itertools.product(range(len(rows) - 1), range(len(cols) - 1)):
            result = inspect(rows[i:i + 2], cols[j:j + 2], receipt["graph"]["primal_edges"])
            count += 1
            bad += not result["simple"]
            pendant += bool(result["pendant_corners"])
            if witness is None and result["pendant_corners"]:
                witness = dict(frequency=receipt["frequency"], row_pair=[i, i + 1],
                               column_pair=[j, j + 1], graph=receipt["graph"], **result)
        summaries.append(dict(frequency=receipt["frequency"], cells=count,
                              nonsimple=bad, pendant_corner_cells=pendant))
    return dict(schema="fourcolor-v24-ordered-mesh-cell-v1", positive=positive,
                spheres=summaries, witness=witness,
                verdict="corner-preserving rim construction refuted" if witness else "controls passed",
                scope="generic ordered-mesh geometry, not target mesh exclusion or a 4CT refutation")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit(json.loads(Path("results/fourcolor/v24_contour_mesh_gate.json").read_text()),
                   json.loads(Path("results/fourcolor/v24_ordered_contour_gate.json").read_text()))
    if args.output:
        atomic_write_json(args.output, result)
    print(json.dumps({k: v for k, v in result.items() if k not in ("witness", "positive")}, indent=2))
    if result["witness"]:
        print(json.dumps({k: v for k, v in result["witness"].items() if k != "graph"}, indent=2))
