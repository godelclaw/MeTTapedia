#!/usr/bin/env python3
"""Replay the exterior arcs forced by short seam faces of padded caps.

These are independent finite program checks. The general connectivity law
and its actual strict-reduction consumer are proved separately in Lean.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

import networkx as nx

from alternating_lobe_probe import data
from padded_cap_geometry_probe import padded, sew, cycle
from padded_cap_recognition_probe import trace

HERE = Path(__file__).resolve().parent
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def exterior_arcs(m, root, graph, vertex, alpha, rho, faces):
    piece, _, base, mapped = trace(m, root, alpha, rho)
    cap = {vertex[d] for d in base.values()}
    assert len(cap) == 8*m
    ports = {j: mapped[d] for j, d in piece["ports"].items()}
    face_of = {d: f for f in faces for d in f}
    phi = lambda d: rho[alpha[d]]
    assert nx.is_connected(graph)
    assert {d for d in alpha if vertex[d] in cap and vertex[alpha[d]] not in cap} == set(ports.values())
    paths, counts = [], Counter()
    for j in range(2*m):
        previous = ports[(j-1) % (2*m)]
        length = len(face_of[previous])
        assert length in (5, 6)
        d, path = previous, []
        for _ in range(length-3):
            d = phi(d)
            assert vertex[d] not in cap
            path.append(vertex[d])
        assert d == alpha[ports[j]]
        assert path[0] == vertex[alpha[previous]]
        assert all(graph.has_edge(a, b) for a, b in zip(path, path[1:]))
        counts[length] += 1
        paths.append(path)
    exterior = graph.subgraph(set(graph)-cap)
    assert nx.is_connected(exterior)
    return dict(sectors=m, arcs_checked=2*m,
                seam_faces={str(k): v for k, v in sorted(counts.items())},
                exterior_connected=True, outside_arc_vertices=paths)


def run(fixtures, controls, recognition):
    raw = json.loads(fixtures.read_text())["maps"] + json.loads(controls.read_text())["controls"]
    by_name = {example["id"]: example for example in raw}
    saved = json.loads(recognition.read_text())
    for dependency in saved["dependencies"]:
        assert dependency["source_sha256"] == hashlib.sha256((HERE/dependency["source"]).read_bytes()).hexdigest()
    actual, literal, totals = [], [], Counter()
    for m in range(2, 21):
        a = padded(m)
        for name, b in (("cap-cap", padded(m)), ("cap-cycle", cycle(2*m))):
            graph, vertex, alpha, faces = sew(a, b)
            rho = {(side, d): (side, e) for side, piece in ((0, a), (1, b))
                   for d, e in piece["rho"].items()}
            result = exterior_arcs(m, (0, ("e", 0, 0, 0)), graph, vertex, alpha, rho, faces)
            totals.update({k: v for k, v in result["seam_faces"].items()})
            result.pop("outside_arc_vertices")
            literal.append(dict(map=name, original_vertices=len(graph), **result))
    for example in saved["actual_candidates"]:
        graph, alpha, rho, faces = data(by_name[example["map"]]["rotation"])
        result = exterior_arcs(example["sectors"], tuple(example["root"]), graph,
                               {d: d[0] for d in alpha}, alpha, rho, faces)
        totals.update({k: v for k, v in result["seam_faces"].items()})
        actual.append(dict(map=example["map"], root=example["root"], **result))
    dependencies = [Path(__file__), fixtures, controls, recognition,
                    HERE/"padded_cap_recognition_probe.py", HERE/"padded_cap_geometry_probe.py",
                    HERE/"padded_cap_probe.py", HERE/"alternating_lobe_probe.py",
                    HERE/"alternating_cycle_probe.py"]
    return dict(evidence="Independent finite program replay; no fixture normal-form, minimality or global coverage certification.",
                dependencies=[dict(source=p.name, source_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                              for p in dependencies],
                seam_faces=dict(sorted(totals.items())), arcs_checked=sum(totals.values()),
                literal_sector_counts=list(range(2, 21)), literal_examples=literal,
                literal_width_two="Parallel edge identity is retained by the rotation data; the general graph-backed Lean consumer has a simple-graph domain.",
                actual_occurrences=len(actual), actual_examples=actual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=HERE/"alternating-lobe-fixtures.json")
    parser.add_argument("--controls", type=Path, default=HERE/"diamond-supply-probe.json")
    parser.add_argument("--recognition", type=Path, default=HERE/"padded-cap-recognition-probe.json")
    parser.add_argument("--output", type=Path, default=HERE/"padded-cap-exterior-probe.json")
    args = parser.parse_args()
    protected = {args.fixtures.resolve(), args.controls.resolve(), args.recognition.resolve(), Path(__file__).resolve()}
    if args.output.resolve() in protected:
        parser.error("The output must not overwrite a program or input.")
    result = run(args.fixtures, args.controls, args.recognition)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ("arcs_checked", "seam_faces", "actual_occurrences")}))


if __name__ == "__main__":
    main()
