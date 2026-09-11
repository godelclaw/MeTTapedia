#!/usr/bin/env python3
"""Test connected-cap surgery on complete distance-contour bands.

Pre-registered checks: spherical cubic controls; all ambient boundary edges;
two nonempty connected caps and their complements; connected middle shell;
the original middle is retained, and every absorbed vertex stays in the
one-layer buffer. Symmetric GP controls are supplemented by an irregular
fullerene and its triangular refinement, on which absorption is nontrivial.
No colouring, ring certificate, or unavoidability catalogue is computed.
"""
import argparse
import itertools
import json
from collections import defaultdict
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_contour_mesh_gate import component, cycle_order, linkage, verify_archive
from v24_geodesic_mincut_gate import boundary_order, connected, validate_sphere
from v24_geodesic_transfer_gate import bfs, face_dual_adjacency
from v24_goldberg import edge_face_adjacency
from v24_plantri_seed_audit import face_cycles
from v24_protected_contour_band_gate import band


# One geometric counterexample, discovered among 5-connected triangulations.
# Its embedding and dual connectivity are independently checked below.
IRREGULAR = [
    [1,2,3],[0,4,5],[0,6,7],[0,8,9],[1,9,10],[1,11,12],
    [2,12,13],[2,14,8],[3,7,15],[3,16,4],[4,17,18],[5,18,19],
    [5,20,6],[6,21,22],[7,22,23],[8,24,16],[9,15,17],[10,16,25],
    [10,26,11],[11,27,20],[12,19,28],[13,28,29],[13,30,14],[14,31,24],
    [15,23,25],[17,24,32],[18,32,27],[19,26,33],[20,33,21],[21,34,30],
    [22,29,31],[23,30,35],[25,35,26],[27,34,28],[29,33,35],[31,34,32]]


def graph_of_rotation(rotation):
    return dict(primal_vertex_count=len(rotation),
                primal_edges=[[u,v] for u,row in enumerate(rotation) for v in row if u<v],
                face_cycles=face_cycles(rotation))


def incidence(g):
    n, edges = g['primal_vertex_count'], g['primal_edges']
    adj = [set() for _ in range(n)]
    for u,v in edges:
        adj[u].add(v)
        adj[v].add(u)
    inc = [{f for f,vs in enumerate(g['face_cycles']) if v in vs} for v in range(n)]
    return adj, inc


def contours(g, root):
    dual, ef = face_dual_adjacency(g), edge_face_adjacency(g)
    ds, _ = bfs(dual, root)
    far = ds.index(max(ds))
    rows = []
    for d in range(max(ds)):
        r = component(dual, {f for f,k in enumerate(ds) if k>d}, far)
        edges = [e for e,(f,h) in ef.items() if (f in r)!=(h in r)]
        rows.append(dict(faces=sorted(r), cycle=cycle_order(g['primal_edges'],edges)))
    return far, rows


def components(adj, allowed):
    todo, result = set(allowed), []
    while todo:
        part = component(adj, todo, min(todo))
        result.append(sorted(part))
        todo -= part
    return result


def check_linkage(g, source, sink, paths, separator):
    """Replay the path packing and separator without trusting the flow solver."""
    adj, _ = incidence(g)
    used = set()
    for path in paths:
        assert path and path[0] in source and path[-1] in sink
        assert len(set(path)) == len(path) and not used.intersection(path)
        assert all(v in adj[u] for u,v in zip(path,path[1:]))
        used.update(path)
    assert len(set(separator)) == len(separator) == len(paths)
    allowed = set(range(g['primal_vertex_count']))-set(separator)
    for start in source & allowed:
        assert not component(adj,allowed,start).intersection(sink)


def refine(g):
    """Subdivide every dual triangle into four, then take the primal dual."""
    _, inc = incidence(g)
    midpoint = {}
    next_vertex = len(g['face_cycles'])

    def half(a,b):
        nonlocal next_vertex
        e = tuple(sorted((a,b)))
        if e not in midpoint:
            midpoint[e] = next_vertex
            next_vertex += 1
        return midpoint[e]

    triangles = []
    for triple in inc:
        a,b,c = sorted(triple)
        ab,bc,ca = half(a,b),half(b,c),half(c,a)
        triangles.extend([(a,ab,ca),(b,bc,ab),(c,ca,bc),(ab,bc,ca)])
    dual_edges = defaultdict(list)
    for v,(a,b,c) in enumerate(triangles):
        for p,q in [(a,b),(b,c),(c,a)]:
            dual_edges[tuple(sorted((p,q)))].append(v)
    assert all(len(vs)==2 for vs in dual_edges.values())
    keys = sorted(dual_edges)
    edges = [dual_edges[e] for e in keys]
    faces = [cycle_order(edges,[i for i,e in enumerate(keys) if f in e])
             for f in range(next_vertex)]
    result = dict(primal_vertex_count=len(triangles), primal_edges=edges, face_cycles=faces)
    validate_sphere(result)
    assert connected(len(triangles),edges,set(range(len(triangles))))
    assert all(len(f) in (5,6) for f in faces)
    return result


def shell_check(g, rows, lo, hi):
    n, edges = g['primal_vertex_count'], g['primal_edges']
    adj, inc = incidence(g)
    vertices = set(range(n))
    regions = [set(r['faces']) for r in rows]
    wide = band(inc,regions[lo],regions[hi])
    middle = band(inc,regions[lo+1],regions[hi-1])
    outer = component(adj,vertices-middle,min(rows[lo]['cycle']))
    inner = component(adj,vertices-middle,min(rows[hi]['cycle']))
    shell = vertices-outer-inner
    assert not outer & inner and middle <= shell <= wide
    assert all(connected(n,edges,s) for s in
               (middle,outer,inner,shell,vertices-outer,vertices-inner))
    assert all(not ((u in outer and v in inner) or (v in outer and u in inner))
               for u,v in edges)
    cut = [(u,v) for u,v in edges if (u in shell)!=(v in shell)]
    assert all((u if u in shell else v) in middle for u,v in cut)
    assert set(rows[lo]['cycle']) <= outer and set(rows[hi]['cycle']) <= inner
    # Each complete cap cut is a dual cycle, not just selected column ends.
    edge_faces = edge_face_adjacency(g)
    for side in (outer, vertices-inner):
        cap_cut = [i for i,(u,v) in enumerate(edges) if (u in side)!=(v in side)]
        boundary_order(edge_faces,cap_cut)
    # The largest allowed marked set: every vertex outside the protected buffer.
    marks = vertices-wide
    assert not shell & marks
    assert all(({v}|adj[v]) <= outer or ({v}|adj[v]) <= inner for v in marks)
    return dict(absorbed=len(shell-middle), full_cut_edges=len(cut), marked_stars=len(marks))


def run(archive):
    verify_archive(archive)
    original = graph_of_rotation(IRREGULAR)
    validate_sphere(original)
    assert connected(36,original['primal_edges'],set(range(36)))
    assert all(len(f) in (5,6) for f in original['face_cycles'])
    dual = face_dual_adjacency(original)
    # Check the generator's claimed connectivity independently of plantri.
    connectivity_checks = 0
    for k in range(5):
        for deleted in itertools.combinations(range(len(dual)),k):
            left = set(range(len(dual)))-set(deleted)
            assert component(dual,left,min(left)) == left
            connectivity_checks += 1
    far, rows = contours(original,13)
    adj, inc = incidence(original)
    middle = band(inc,set(rows[1]['faces']),set(rows[2]['faces']))
    caps = components(adj,set(range(36))-middle)
    assert len(caps)==3
    paths, separator = linkage(36,original['primal_edges'],set(rows[1]['cycle']),set(rows[2]['cycle']))
    check_linkage(original,set(rows[1]['cycle']),set(rows[2]['cycle']),paths,separator)
    assert len(paths)==len(separator)==8
    negative = dict(graph=original, root=13, far=far, depths=[1,2],
                    band=sorted(middle), complement_components=caps,
                    contours=[rows[1],rows[2]], linkage=paths, separator=separator)
    positive = []
    families = [(f'GP({r["frequency"]},0)',r['graph'],[0]) for r in archive['receipts']]
    refined = refine(original)
    families.append(('irregular-refinement',refined,range(len(refined['face_cycles']))))
    for name,g,roots in families:
        totals = dict(windows=0, changed_windows=0, absorbed_vertices=0, full_cut_edges=0, marked_stars=0)
        for root in roots:
            _, rows = contours(g,root)
            for lo in range(len(rows)):
                for hi in range(lo+3,len(rows)):
                    result = shell_check(g,rows,lo,hi)
                    totals['windows'] += 1
                    totals['changed_windows'] += result['absorbed']>0
                    totals['absorbed_vertices'] += result['absorbed']
                    totals['full_cut_edges'] += result['full_cut_edges']
                    totals['marked_stars'] += result['marked_stars']
        positive.append(dict(family=name,vertices=g['primal_vertex_count'],**totals))
    assert positive[-1]['changed_windows']>0
    return dict(schema='fourcolor-v24-buffered-shell-v1', negative=negative,
                dual_connectivity_checks=connectivity_checks, positive=positive,
                scope='complete geometric shell and cap checks; no shrinking or colouring claim')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archive',type=Path)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    result = run(json.loads(args.archive.read_text()))
    if args.output:
        atomic_write_json(args.output,result)
    print(json.dumps(result,sort_keys=True))


if __name__=='__main__':
    main()
