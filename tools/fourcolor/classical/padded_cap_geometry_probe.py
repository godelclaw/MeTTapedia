#!/usr/bin/env python3
"""Replay literal cap replacement geometry and a 96-vertex fullerene example.

Independent finite checks of darts, rotations, bridge-freedom, whole-map
size and colour reconstruction. These are not Lean certificates.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json

import networkx as nx

from alternating_cycle_probe import cycles
from alternating_lobe_probe import tait_colouring
from padded_cap_probe import cap_geometry, reconstruct

HERE = Path(__file__).resolve().parent
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def finish(stars, alpha, ports):
    vertex, rho = {}, {}
    for v, ds in stars.items():
        assert len(ds) == 3 and len(set(ds)) == 3
        for j, d in enumerate(ds):
            assert d not in vertex
            vertex[d] = v
            rho[d] = ds[(j+1) % 3]
    assert set(vertex) == set(alpha) | set(ports.values())
    for d, e in alpha.items():
        assert d != e and alpha[e] == d and vertex[d] != vertex[e]
    phi = {d: rho[alpha.get(d,d)] for d in vertex}
    faces = cycles(phi)
    reverse = {d:j for j,d in ports.items()}
    for j,d in ports.items():
        q = phi[d]
        while q not in reverse:
            q = phi[q]
        assert reverse[q] == (j-1) % len(ports)
    return dict(vertex=vertex, rho=rho, alpha=alpha, ports=ports, faces=faces)


def padded(m):
    edge = lambda i,e,b: ("e",i % m,e,b)
    port = lambda j: ("p",j % (2*m))
    stars = {}
    for i in range(m):
        stars.update({
            (i,0): [edge(i-1,0,1),edge(i,0,0),edge(i,3,0)],
            (i,1): [edge(i-1,1,1),edge(i,3,1),edge(i,4,0)],
            (i,2): [edge(i,4,1),edge(i,5,0),edge(i,6,0)],
            (i,3): [edge(i,5,1),edge(i,1,0),edge(i,7,0)],
            (i,4): [edge(i-1,2,1),edge(i,6,1),edge(i,8,0)],
            (i,5): [edge(i,8,1),edge(i,9,0),port(2*i)],
            (i,6): [edge(i,9,1),edge(i,7,1),edge(i,10,0)],
            (i,7): [edge(i,10,1),edge(i,2,0),port(2*i+1)]})
    alpha = {edge(i,e,b):edge(i,e,1-b) for i in range(m) for e in range(11) for b in (0,1)}
    p = finish(stars,alpha,{j:port(j) for j in range(2*m)})
    assert len(p["faces"]) == 3*m+2
    # Verify the edge incidences against the independently used colour model.
    _, ends, _ = cap_geometry(m)
    assert all((p["vertex"][edge(i,e,0)],p["vertex"][edge(i,e,1)]) == uv
               for (i,e),uv in ends.items())
    return p


def cycle(n):
    edge = lambda i,b: ("e",i % n,b)
    port = lambda i: ("p",i)
    stars = {i:[port(i),edge(i,0),edge(i+1,1)] for i in range(n)}
    alpha = {edge(i,b):edge(i,1-b) for i in range(n) for b in (0,1)}
    p = finish(stars,alpha,{j:port(j) for j in range(n)})
    assert len(p["faces"]) == 2
    return p


def sew(left,right):
    n = len(left["ports"])
    assert n == len(right["ports"])
    vertex, rho, alpha = {}, {}, {}
    for side,p in enumerate((left,right)):
        vertex.update({(side,d):(side,v) for d,v in p["vertex"].items()})
        rho.update({(side,d):(side,e) for d,e in p["rho"].items()})
        alpha.update({(side,d):(side,e) for d,e in p["alpha"].items()})
    for j in range(n):
        d,e = (0,left["ports"][j]),(1,right["ports"][(-j) % n])
        alpha[d],alpha[e] = e,d
    graph = nx.MultiGraph()
    visited = set()
    for d,e in alpha.items():
        if d not in visited:
            graph.add_edge(vertex[d],vertex[e])
            visited.update((d,e))
    faces = cycles({d:rho[alpha[d]] for d in vertex})
    assert all(alpha[alpha[d]] == d and alpha[d] != d for d in alpha)
    bridges = [(u,v) for u,v in nx.bridges(nx.Graph(graph)) if graph.number_of_edges(u,v) == 1]
    assert nx.is_connected(graph) and not bridges
    assert all(deg == 3 for _,deg in graph.degree())
    assert len(graph)-graph.number_of_edges()+len(faces) == 2
    return graph,vertex,alpha,faces


def check(m):
    cap, small = padded(m),cycle(2*m)
    old,_,_,old_faces = sew(cap,cap)
    new,_,_,new_faces = sew(cap,small)
    assert (len(old),len(new)) == (16*m,10*m)
    return dict(sectors=m, old_vertices=len(old), smaller_vertices=len(new), vertex_loss=6*m,
                open_cap_faces=len(cap["faces"]), open_cycle_faces=len(small["faces"]),
                old_face_lengths=dict(sorted(Counter(map(len,old_faces)).items())),
                smaller_face_lengths=dict(sorted(Counter(map(len,new_faces)).items())),
                spherical_cubic_connected_bridgeless=True)


def coloured_example(m=6):
    cap = padded(m)
    new,vs,al,_ = sew(cap,cycle(2*m))
    old,vo,ao,faces = sew(cap,cap)
    assert new.number_of_edges() == nx.Graph(new).number_of_edges()
    assigned = tait_colouring(nx.Graph(new))
    colours = {frozenset((u,v)):c+1 for u,v,c in assigned}
    small_colour = {d:colours[frozenset((vs[d],vs[al[d]]))] for d in vs}
    word = tuple(small_colour[1,("p",j)] for j in range(2*m))
    seams = tuple(small_colour[1,("e",2*i,0)] for i in range(m))
    internal,q = reconstruct(word,seams)
    restored = {}
    for side,d in vo:
        if side == 0:
            restored[side,d] = small_colour[side,d]
        elif d[0] == "p":
            restored[side,d] = word[d[1]]
        else:
            restored[side,d] = internal[d[1],d[2]]
    assert all(restored[d] == restored[ao[d]] for d in vo)
    for v in old:
        assert {restored[d] for d in vo if vo[d] == v} == {1,2,3}
    assert all(restored[d] == small_colour[d] for d in vo if d[0] == 0)
    assert set(map(len,faces)) <= {5,6}
    return dict(sectors=m, original_vertices=len(old), smaller_vertices=len(new),
                old_face_lengths=dict(sorted(Counter(map(len,faces)).items())),
                boundary_word=word, source_seams=seams, shared_radial_choices=q,
                original_all_faces_five_or_six=True, exterior_darts_preserved=24*m,
                reconstructed_proper_colouring=True,
                recognition_evidence="Explicit literal sewing; no general coverage claim.")


def main():
    report = dict(evidence="Independent finite program checks, not Lean certificates.",
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  geometry=[check(m) for m in range(2,21)], example=coloured_example())
    (HERE / "padded-cap-geometry-probe.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(geometries_checked=len(report["geometry"]),example=report["example"])))


if __name__ == "__main__":
    main()
