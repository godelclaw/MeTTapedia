#!/usr/bin/env python3
"""Replay the actual face trace and shore recognition of padded caps.

Finite program evidence, separate from the Lean family proofs. The saved
maps test geometric hypotheses; they do not establish global coverage.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

import networkx as nx

from alternating_lobe_probe import data
from padded_cap_geometry_probe import padded, sew

HERE = Path(__file__).resolve().parent
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def source_slots(p, m):
    codes = [0, 1, 4, 5, 2, 8, 9, 10]
    result = {}
    for i in range(m):
        for v in range(8):
            d = ("e", (i-1) % m if v in (0, 1, 4) else i, codes[v], 1)
            for s in range(3):
                assert p["vertex"][d] == (i, v)
                result[d] = (i, v, s)
                d = p["rho"][d]
    assert set(result) == set(p["vertex"])
    return result


def trace(m, root, alpha, rho):
    phi = lambda d: rho[alpha[d]]
    center, d = [], root
    for _ in range(m):
        center.append(d)
        d = phi(d)
    base = {}
    for i, c in enumerate(center):
        incoming = alpha[rho[c]]
        middle = alpha[rho[incoming]]
        last_middle = alpha[rho[middle]]
        outer_incoming = alpha[rho[rho[middle]]]
        outer_first = alpha[rho[outer_incoming]]
        outer_middle = alpha[rho[rho[last_middle]]]
        outer_last = alpha[rho[outer_middle]]
        row = [rho[rho[c]], rho[rho[incoming]], middle, last_middle,
               rho[rho[outer_incoming]], outer_first,
               rho[rho[outer_middle]], outer_last]
        base.update({(i, v): x for v, x in enumerate(row)})
    p = padded(m)
    mapped = {}
    for d, (i, v, s) in source_slots(p, m).items():
        x = base[i, v]
        for _ in range(s):
            x = rho[x]
        mapped[d] = x
    return p, center, base, mapped


def recognize(m, root, graph, vertex, alpha, rho, faces):
    p, center, base, mapped = trace(m, root, alpha, rho)
    face_of = {d: f for f in faces for d in f}
    lengths = [len(face_of[root])] + [len(face_of[alpha[c]]) for c in center]
    lengths += [len(face_of[base[i, 1]]) for i in range(m)]
    lengths += [len(face_of[base[i, 3]]) for i in range(m)]
    if lengths != [m] + [6]*(2*m) + [5]*m:
        return None
    assert all(mapped[e] == rho[mapped[d]] for d, e in p["rho"].items())
    assert all(mapped[e] == alpha[mapped[d]] for d, e in p["alpha"].items())
    image = {v: vertex[d] for v, d in base.items()}
    assert all(vertex[mapped[d]] == image[p["vertex"][d]] for d in mapped)
    keep = set(image.values())
    injective = len(keep) == 8*m
    ports = {j: mapped[d] for j, d in p["ports"].items()}
    short = all(len(face_of[d]) in (5, 6) for d in ports.values())
    exposed = all(vertex[alpha[d]] not in keep for d in ports.values())
    if injective and short:
        assert exposed
    if injective and exposed:
        assert {d for d in alpha if vertex[d] in keep} == set(mapped.values())
        assert {d for d in alpha if vertex[d] in keep and vertex[alpha[d]] not in keep} == set(ports.values())
    outside = graph.subgraph(set(graph)-keep)
    connected = bool(outside) and nx.is_connected(outside)
    return dict(sectors=m, face_lengths=lengths,
                trace_vertices=len(keep), distinct_vertices=injective,
                boundary_short_faces=short, exposed_ports=exposed,
                exterior_connected=connected,
                cap_vertex_correspondence=[[i, v, image[i, v]] for i in range(m) for v in range(8)],
                exterior_vertices=len(outside),
                boundary_ports=len(ports),
                proposed_smaller_vertices=len(graph)-8*m+2*m if injective else None)


def literal(m):
    p = padded(m)
    graph, vertex, alpha, faces = sew(p, p)
    rho = {(side, d): (side, e) for side in (0, 1) for d, e in p["rho"].items()}
    result = recognize(m, (0, ("e", 0, 0, 0)), graph, vertex, alpha, rho, faces)
    assert result and all(result[k] for k in
                          ("distinct_vertices", "boundary_short_faces", "exposed_ports", "exterior_connected"))
    result.pop("cap_vertex_correspondence")
    return dict(original_vertices=len(graph), **result)


def run(fixtures, controls):
    raw = json.loads(fixtures.read_text())["maps"] + json.loads(controls.read_text())["controls"]
    candidates, checked_faces = [], 0
    for example in raw:
        graph, alpha, rho, faces = data(example["rotation"])
        vertex = {d: d[0] for d in alpha}
        for face in faces:
            m = len(face)
            checked_faces += 1
            result = recognize(m, face[0], graph, vertex, alpha, rho, faces)
            if result:
                candidates.append(dict(map=example["id"], original_vertices=len(graph),
                                       root=list(face[0]), **result))
    counts = Counter((r["distinct_vertices"], r["boundary_short_faces"],
                      r["exposed_ports"], r["exterior_connected"]) for r in candidates)
    dependencies = [Path(__file__), fixtures, controls,
                    HERE/"padded_cap_geometry_probe.py", HERE/"padded_cap_probe.py",
                    HERE/"alternating_lobe_probe.py", HERE/"alternating_cycle_probe.py"]
    return dict(evidence="Independent finite program replay; no Lean certificates or global coverage claim.",
                dependencies=[dict(source=p.name, source_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                              for p in dependencies],
                maps_checked=len(raw), actual_faces_checked=checked_faces,
                actual_cap_candidates=len(candidates),
                hypothesis_counts=[dict(distinct_vertices=a, short_boundary_faces=b,
                                        exposed_ports=c, exterior_connected=d, occurrences=count)
                                   for (a, b, c, d), count in sorted(counts.items())],
                literal_families=[literal(m) for m in range(2, 21)],
                actual_candidates=candidates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=HERE/"alternating-lobe-fixtures.json")
    parser.add_argument("--controls", type=Path, default=HERE/"diamond-supply-probe.json")
    parser.add_argument("--output", type=Path, default=HERE/"padded-cap-recognition-probe.json")
    args = parser.parse_args()
    if args.output.resolve() in {args.fixtures.resolve(), args.controls.resolve(), Path(__file__).resolve()}:
        parser.error("The output must not overwrite a program or input.")
    result = run(args.fixtures, args.controls)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ("maps_checked", "actual_faces_checked",
                                          "actual_cap_candidates", "hypothesis_counts")}))
    print("Literal family members checked:", len(result["literal_families"]))


if __name__ == "__main__":
    main()
