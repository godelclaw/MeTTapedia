#!/usr/bin/env python3
"""Replay the prism's inverse recognition and recovered cyclic-cut domain.

The fixture is constructed from a compact source rotation. Recognition then
receives only the actual target rotation. Cut and retained-connectivity
observations are evaluated on the recovered source. No source colour word
or Four Colour endpoint is used.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import re

import networkx as nx

from dual_truncate_geometry_probe import rotation_data
from dual_truncate_inverse_probe import recognize
from alternating_cycle_probe import cycles

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def fixture():
    text = (LEAN / "DualTruncateSourceDomainExample.lean").read_text()
    table = re.search(r"neighbours\s*:=.*?ByteArray\.mk\s*#\[(.*?)\]", text, re.S)
    assert table
    flat = bytes(map(int, re.findall(r"\d+", table.group(1))))
    neighbours = [int.from_bytes(flat[i:i + 2], "little") for i in range(0, len(flat), 2)]
    assert len(neighbours) == 18
    source = ";".join(",".join(map(str, neighbours[i:i + 3])) for i in range(0, 18, 3))
    _, alpha, rho = rotation_data(source)
    phi = {d: rho[alpha[d]] for d in alpha}
    inverse = {e: d for d, e in phi.items()}
    darts = sorted(alpha)
    ids = {d: i for i, d in enumerate(darts)}
    return ";".join(",".join(str(ids[e]) for e in (alpha[d], phi[d], inverse[d]))
                    for d in darts)


def run():
    raw = fixture()
    recognized = recognize("triangular-prism-target", raw)
    assert recognized["recognized"]
    graph, alpha, rho = rotation_data(recognized["recovered_source_rotation"])
    assert len(graph) == 6 and all(degree == 3 for _, degree in graph.degree())
    assert nx.node_connectivity(graph) == 3
    cuts = []
    vertices = sorted(graph)
    for mask in range(1 << len(vertices)):
        inside = {v for i, v in enumerate(vertices) if mask & (1 << i)}
        outside = set(vertices) - inside
        if nx.cycle_basis(graph.subgraph(inside)) and nx.cycle_basis(graph.subgraph(outside)):
            crossing = sorted([min(u, v), max(u, v)] for u, v in graph.edges
                              if (u in inside) != (v in inside))
            cuts.append(dict(inside=sorted(inside), crossing=crossing, size=len(crossing)))
    cut = min(cuts, key=lambda item: (item["size"], item["inside"]))
    assert cut["size"] == 3
    choices = [dict(pair=[a, b], root=r) for r in vertices
               for a, b in itertools.combinations(sorted(graph[r]), 2)
               if not graph.has_edge(a, b)
               and nx.is_connected(graph.subgraph(set(vertices) - {a, b}))]
    assert choices
    actual, ta, tr = rotation_data(raw)
    target_faces = cycles({d: tr[ta[d]] for d in ta})
    assert Counter(map(len, target_faces)) == {3: 2, 4: 3, 6: 6}
    paths = [Path(__file__), HERE / "dual_truncate_inverse_probe.py",
             HERE / "dual_truncate_geometry_probe.py", HERE / "alternating_cycle_probe.py",
             LEAN / "DualTruncateSourceDomainExample.lean", LEAN / "CyclicEdgeCutIso.lean",
             LEAN / "DualTruncateSourceDomainAudit.lean",
             LEAN / "DualTruncateInverseRoundTrip.lean"]
    return dict(status="independent recovered-source domain replay",
                target_rotation=raw, recognition=recognized,
                target_face_lengths=dict(sorted(Counter(map(len, target_faces)).items())),
                target_connected=nx.is_connected(actual),
                recovered_source_rotation=recognized["recovered_source_rotation"],
                recovered_source_cyclic_cut=cut, recovered_source_cyclic_connectivity=3,
                recovered_source_vertex_connectivity=3, compatible_coupled_choices=choices,
                kernel_cut_obstruction_proved=True,
                kernel_target_geometry_and_reconstruction_proved=True,
                kernel_every_complete_GSLT_sweep_supported=True,
                source_colour_words_read=0,
                target_recognition_saved_source_rotations_read=0,
                cyclic_four_supplier_used=False,
                normal_form_pentagonal_hexagonal_domain=False,
                new_catalogue_entries_removed=0, global_coverage_proved=False,
                input_sha256={p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in paths})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "dual-truncate-source-domain-probe.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report = run()
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.check:
        assert args.output.read_text() == text, "Source-domain replay receipt differs."
    else:
        args.output.write_text(text)
    print(json.dumps(dict(target_vertices=report["recognition"]["target_vertices"],
                          recovered_vertices=len(rotation_data(report["recovered_source_rotation"])[0]),
                          cyclic_cut_size=report["recovered_source_cyclic_cut"]["size"],
                          compatible_coupled_choices=len(report["compatible_coupled_choices"]))))


if __name__ == "__main__":
    main()
