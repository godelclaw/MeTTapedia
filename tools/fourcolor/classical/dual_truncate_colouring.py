#!/usr/bin/env python3
"""Replay the local vertex-to-edge rule on five saved residual maps.

The uniform rule is proved separately in Lean. These checks validate concrete
source colourings and exact dart/rotation adapters to the saved target maps;
they are independent program evidence, not kernel certificates of those inputs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from alternating_lobe_probe import data

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def examine(source, target, witness):
    assert target["id"] == "dual-truncate-" + source["id"]
    graph, alpha, rho, faces = data(source["rotation"])
    expanded, target_alpha, target_rho, _ = data(target["rotation"])
    colour = list(map(int, witness["vertex_colour_word"]))
    assert len(colour) == len(graph)
    assert set(colour) <= {1, 2, 3}
    assert all(colour[u] != colour[v] for u, v in graph.edges())
    phi = {d: rho[alpha[d]] for d in alpha}
    inverse = {e: d for d, e in phi.items()}
    assert len(inverse) == len(phi)
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    labels = sorted({(face_of[d], face_of[alpha[d]]) for d in alpha})
    ids = {label: i for i, label in enumerate(labels)}
    vertex = {d: ids[face_of[d], face_of[alpha[d]]] for d in alpha}
    assert len(set(vertex.values())) == len(alpha) == len(expanded)
    assert set(vertex.values()) == set(expanded)
    neighbours = {d: (alpha[d], phi[d], inverse[d]) for d in alpha}

    def image(d, slot):
        return vertex[d], vertex[neighbours[d][slot]]

    edges = {}
    for d in sorted(alpha):
        a, b = (colour[v] for v in d)
        star = (a ^ b, b, a)
        assert set(star) == {1, 2, 3}
        assert {vertex[v] for v in neighbours[d]} == set(expanded[vertex[d]])
        mates = ((alpha[d], 0), (phi[d], 2), (inverse[d], 1))
        for slot in range(3):
            dart = image(d, slot)
            assert target_rho[dart] == image(d, (slot + 1) % 3)
            assert target_alpha[dart] == image(*mates[slot])
            edge = tuple(sorted(dart))
            assert edges.setdefault(edge, star[slot]) == star[slot]
    ordered = sorted(tuple(sorted(edge)) for edge in expanded.edges())
    assert set(edges) == set(ordered)
    assert all({edges[tuple(sorted((v, w)))] for w in expanded[v]} == {1, 2, 3}
               for v in expanded)
    assert len(expanded) == 3 * len(graph)
    return dict(source=source["id"], target=target["id"],
                source_vertices=len(graph), target_vertices=len(expanded),
                target_edges=len(edges), target_darts_checked=3 * len(expanded),
                vertex_adapter_word=",".join(str(vertex[d]) for d in sorted(alpha)),
                edge_colour_word="".join(str(edges[edge]) for edge in ordered),
                rotation_orientation=1, kernel_input_certificate=False,
                source_rotation_sha256=hashlib.sha256(source["rotation"].encode()).hexdigest(),
                target_rotation_sha256=hashlib.sha256(target["rotation"].encode()).hexdigest())


def run(fixtures):
    witnesses = json.loads(fixtures.read_text())["maps"]
    sources = {m["id"]: m for m in json.loads((HERE / "family-supply-fixtures.json").read_text())["maps"]}
    saved = json.loads((HERE / "family-supply-probe.json").read_text())
    targets = {m["id"]: m for m in saved["maps"]}
    assert len(witnesses) == len(saved["failed_map_ids"])
    assert {m["target"] for m in witnesses} == set(saved["failed_map_ids"])
    results = [examine(sources[w["source"]], targets[w["target"]], w) for w in witnesses]
    inputs = [fixtures, HERE / "family-supply-fixtures.json", HERE / "family-supply-probe.json",
              Path(__file__), HERE / "alternating_lobe_probe.py", HERE / "alternating_cycle_probe.py",
              REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/DualTruncateColoring.lean",
              REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/DualTruncateConstructionGSLT.lean",
              REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/DualTruncateColoringAudit.lean"]
    return dict(scope="Five colourable residuals of the current recognized family union.",
                rule="At source dart v->w, the expanded star colours are c(v) XOR c(w), c(w), c(v).",
                maps_checked=len(results),
                source_vertices=sum(m["source_vertices"] for m in results),
                target_vertices=sum(m["target_vertices"] for m in results),
                target_edges=sum(m["target_edges"] for m in results),
                target_darts_checked=sum(m["target_darts_checked"] for m in results),
                maps=results, kernel_input_certificates=False,
                universal_source_three_colouring_asserted=False, global_coverage_proved=False,
                source_sha256={str(p.relative_to(REPO)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in inputs})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=HERE / "dual-truncate-colouring-fixtures.json")
    parser.add_argument("--output", type=Path, default=HERE / "dual-truncate-colouring.json")
    args = parser.parse_args()
    inputs = {args.fixtures.resolve(), Path(__file__).resolve(),
              (HERE / "family-supply-fixtures.json").resolve(), (HERE / "family-supply-probe.json").resolve()}
    assert args.output.resolve() not in inputs
    result = run(args.fixtures)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("maps_checked", "source_vertices", "target_vertices",
                                           "target_edges", "target_darts_checked")}))


if __name__ == "__main__":
    main()
