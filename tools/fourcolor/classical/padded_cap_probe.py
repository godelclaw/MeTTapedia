#!/usr/bin/env python3
"""Replay uniform padded-cap colourings and an actual GP(2,0) replacement.

Independent finite program evidence. The Lean family theorem reconstructs
nonconstant cycle boundary words, and all words for even sector counts.
The support census also retains the odd-width monochromatic failures.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

import networkx as nx

from alternating_lobe_probe import data, tait_colouring
from alternating_cycle_probe import cycles as permutation_cycles

HERE = Path(__file__).resolve().parent
COLOURS = (1, 2, 3)

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def cycle_colourings(n):
    def extend(word):
        if len(word) == n:
            if word[-1] != word[0]:
                yield tuple(word)
            return
        for c in COLOURS:
            if c != word[-1]:
                yield from extend(word + [c])
    for c in COLOURS:
        yield from extend([c])


def cap_accepts(word):
    prefixes, total = {0}, 0
    for c in word:
        total ^= c
        prefixes.add(total)
    return total == 0 and len(prefixes) < 4


def boundary_census(m):
    inner_support = set()
    for edges in cycle_colourings(3*m):
        inward = tuple(edges[(3*i-1) % (3*m)] ^ edges[3*i] for i in range(m))
        if cap_accepts(inward):
            inner_support.add(tuple(edges[(j-1) % (3*m)] ^ edges[j]
                                    for j in range(3*m) if j % 3))
    padded = set()
    for edges in cycle_colourings(4*m):
        a, b = edges[::2], edges[1::2]
        inward = tuple(a[i] ^ b[(i-1) % (2*m)] for i in range(2*m))
        if inward in inner_support:
            padded.add(tuple(a[i] ^ b[i] for i in range(2*m)))
    small = {tuple(es[i] ^ es[(i+1) % (2*m)] for i in range(2*m))
             for es in cycle_colourings(2*m)}
    rejected = small - padded
    expected = {tuple([c] * (2*m)) for c in COLOURS} if m % 2 else set()
    assert rejected == expected
    return {"sectors": m, "inner_cap_support": len(inner_support),
            "padded_cap_support": len(padded), "cycle_support": len(small),
            "rejected_cycle_words": sorted(rejected)}


def cap_geometry(m):
    ends, stars = {}, {}
    for i in range(m):
        j, p = (i+1) % m, (i-1) % m
        es = [((i,0),(j,0)), ((i,3),(j,1)), ((i,7),(j,4)),
              ((i,0),(i,1)), ((i,1),(i,2)), ((i,2),(i,3)),
              ((i,2),(i,4)), ((i,3),(i,6)), ((i,4),(i,5)),
              ((i,5),(i,6)), ((i,6),(i,7))]
        for e, uv in enumerate(es):
            ends[i,e] = uv
        stars[i,0] = [(p,0),(j,0),(i,1)]
        stars[i,1] = [(p,3),(i,0),(i,2)]
        stars[i,2] = [(i,1),(i,3),(i,4)]
        stars[i,3] = [(i,2),(j,1),(i,6)]
        stars[i,4] = [(p,7),(i,2),(i,5)]
        stars[i,5] = [(i,4),(i,6),("port",2*i)]
        stars[i,6] = [(i,5),(i,3),(i,7)]
        stars[i,7] = [(i,6),(j,4),("port",2*i+1)]
    return nx.Graph(list(ends.values())), ends, stars


def reconstruct(word, seams):
    m = len(seams)
    assert len(word) == 2*m and (len(set(word)) > 1 or m % 2 == 0)
    assert all(seams[i] in COLOURS and seams[i] != word[2*i] and
               seams[(i+1) % m] == seams[i] ^ word[2*i] ^ word[2*i+1]
               for i in range(m))
    forbidden = word[::2]
    q = [0]*m
    if len(set(forbidden)) == 1:
        assert m % 2 == 0
        a, b = (c for c in COLOURS if c != forbidden[0])
        q = [a if i % 2 == 0 else b for i in range(m)]
    else:
        cut = next(i for i in range(m) if forbidden[i] != forbidden[(i-1) % m])
        q[cut] = forbidden[(cut-1) % m]
        for offset in range(1, m):
            i = (cut+offset) % m
            q[i] = next(c for c in COLOURS if c not in (q[(i-1) % m], forbidden[i]))
    assert all(q[i] in COLOURS and q[i] != q[(i-1) % m] and q[i] != forbidden[i]
               for i in range(m))
    edges = {}
    for i in range(m):
        a, b, s = word[2*i], word[2*i+1], seams[i]
        p, r = q[(i-1) % m], q[i]
        colours = [r, r, seams[(i+1) % m], p ^ r, r, r ^ a, a, a, s ^ a, s, s ^ a]
        for e, c in enumerate(colours):
            assert c in COLOURS
            edges[i,e] = c
        # Each triple is an actual cyclic star from PaddedCycleCapTangle.
        triples = [(p,r,p ^ r), (p,p ^ r,r), (r,r ^ a,a), (r ^ a,r,a),
                   (s,a,s ^ a), (s ^ a,s,a), (s,a,s ^ a),
                   (s ^ a,seams[(i+1) % m],b)]
        assert all(set(t) == set(COLOURS) for t in triples)
    return edges, q


def exhaustive(m):
    checked, constant = 0, 0
    for edges in cycle_colourings(2*m):
        word = tuple(edges[i] ^ edges[(i+1) % (2*m)] for i in range(2*m))
        if len(set(word)) == 1:
            constant += 1
            if m % 2 == 0:
                reconstruct(word, edges[::2])
        else:
            reconstruct(word, edges[::2])
            checked += 1
    assert checked + constant == 2**(2*m) + 2 and constant == 6
    return {"sectors": m, "source_cycle_colourings": checked + constant,
            "nonconstant_reconstructions": checked,
            "constant_reconstructions": constant if m % 2 == 0 else 0,
            "outside_guard": constant if m % 2 else 0}


def physical(raw):
    graph, alpha, rho, faces = data(raw["rotation"])
    root = [d[0] for d in next(face for face in faces if len(face) == 5)]
    distance = nx.multi_source_dijkstra_path_length(graph, root, weight=lambda u,v,d: 1)
    keep = {v for v,d in distance.items() if d <= 4}
    cap, ends, stars = cap_geometry(5)
    actual = graph.subgraph(keep).copy()
    for v in actual:
        actual.nodes[v]["root"] = v in root
    for v in cap:
        cap.nodes[v]["root"] = v[1] == 0
    matcher = nx.isomorphism.GraphMatcher(cap, actual,
        node_match=lambda a,b: a["root"] == b["root"])
    for phi in matcher.isomorphisms_iter():
        ports = {2*i+b: next(iter(set(graph[phi[i,5+2*b]])-keep))
                 for i in range(5) for b in (0,1)}
        def image(v):
            return ports[v[1]] if v[0] == "port" else phi[v]
        if all(rho[phi[v],image(row[j])] == (phi[v],image(row[(j+1) % 3]))
               for v,row in stars.items() for j in range(3)):
            break
    else:
        raise AssertionError("No orientation-preserving cap correspondence")
    rows = [[int(v) for v in row.split(",")] for row in raw["rotation"].split(";")]
    external = sorted(set(graph)-keep)
    new = {i: len(graph)+i for i in range(10)}
    redirect = {(ports[2*i+b],phi[i,5+2*b]): new[2*i+b]
                for i in range(5) for b in (0,1)}
    small_rows = {v: [redirect.get((v,w),w) for w in rows[v]] for v in external}
    small_rows.update({new[i]: [ports[i],new[(i-1) % 10],new[(i+1) % 10]] for i in range(10)})
    small = nx.Graph((v,w) for v,row in small_rows.items() for w in row)
    sa = {(v,w): (w,v) for v,row in small_rows.items() for w in row}
    sr = {(v,w): (v,row[(j+1) % 3]) for v,row in small_rows.items() for j,w in enumerate(row)}
    small_faces = permutation_cycles({d: sr[sa[d]] for d in sa})
    assert all(len(row) == len(set(row)) == 3 for row in small_rows.values())
    assert nx.is_connected(small) and not list(nx.bridges(small))
    assert len(small)-small.number_of_edges()+len(small_faces) == 2
    chosen = tait_colouring(small)
    cs = {frozenset((u,v)): c+1 for u,v,c in chosen}
    word = tuple(cs[frozenset((ports[i],new[i]))] for i in range(10))
    seams = tuple(cs[frozenset((new[(2*i-1) % 10],new[2*i]))] for i in range(5))
    colours, q = reconstruct(word, seams)
    restored = {e:c for e,c in cs.items() if set(e) <= set(external)}
    for (i,e),(u,v) in ends.items():
        restored[frozenset((phi[u],phi[v]))] = colours[i,e]
    for i in range(5):
        for b in (0,1):
            restored[frozenset((phi[i,5+2*b],ports[2*i+b]))] = word[2*i+b]
    assert set(restored) == {frozenset(e) for e in graph.edges()}
    assert all({restored[frozenset((v,w))] for w in graph[v]} == set(COLOURS) for v in graph)
    exterior_darts = {d for d in alpha if d[0] not in keep}
    assert all(restored[frozenset((v,w))] == cs[frozenset((v,redirect.get((v,w),w)))]
               for v,w in exterior_darts)
    assert len(graph)-len(small) == 6*5
    return {"map": raw["id"], "original_vertices": len(graph), "cap_vertices": len(keep),
            "replacement_vertices": 10, "smaller_vertices": len(small), "vertex_loss": 30,
            "oriented_cap_embedding": [[i,v,phi[i,v]] for i in range(5) for v in range(8)],
            "outside_neighbours": [ports[i] for i in range(10)], "boundary_word": word,
            "source_seams": seams, "shared_radial_choices": q,
            "small_rotation": [[v,*small_rows[v]] for v in sorted(small_rows)],
            "small_face_lengths": dict(sorted(Counter(map(len,small_faces)).items())),
            "small_colour_edges": [[u,v,c+1] for u,v,c in chosen],
            "restored_colour_edges": [[*sorted(e),c] for e,c in sorted(restored.items(),
                                                                      key=lambda ec: sorted(ec[0]))],
            "exterior_darts_preserved": len(exterior_darts),
            "connected_cubic_bridgeless_spherical": True,
            "minimality_certified": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=HERE / "diamond-supply-probe.json")
    parser.add_argument("--output", type=Path, default=HERE / "padded-cap-probe.json")
    args = parser.parse_args()
    if args.output.resolve() in {args.input.resolve(), Path(__file__).resolve()}:
        parser.error("The output must not overwrite the program or input.")
    raw = next(r for r in json.loads(args.input.read_text())["controls"] if r["id"] == "Goldberg-GP(2,0)")
    report = {"evidence": "Independent finite program replay, not a Lean certificate.",
              "program_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "input_sha256": hashlib.sha256(args.input.read_bytes()).hexdigest(),
              "boundary_census": [boundary_census(m) for m in (3,4,5)],
              "uniform_formula": [exhaustive(m) for m in range(2,9)],
              "physical": physical(raw)}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"formula_reconstructions": sum(r["nonconstant_reconstructions"]
                                                   for r in report["uniform_formula"]),
                      "constant_reconstructions": sum(r["constant_reconstructions"]
                                                       for r in report["uniform_formula"]),
                      "physical_vertex_loss": report["physical"]["vertex_loss"],
                      "exterior_darts_preserved": report["physical"]["exterior_darts_preserved"],
                      "rejected_cycle_words": [len(r["rejected_cycle_words"])
                                               for r in report["boundary_census"]]}))


if __name__ == "__main__":
    main()
