#!/usr/bin/env python3
"""Preregistered full-cut gate for dual BFS trees and primal cotrees.

On GP(k,0), k=1..8, and annuli of thickness 1..4 and circumference
8,16,32,64, test three deterministic dual roots (deduplicated). Keep
original edge identities throughout. The complement of the dual BFS tree
must be a primal spanning tree. Every fundamental primal cut must equal
the full dual fundamental cycle, with width <= 2*dual_height+1.
Check both induced shores, boundary cycle order, the two facial return
permutations, literal middle width and strict nesting along a longest
primal tree path. Record which nested cuts have cycles on both shores.

Outcomes: cotree_failure, full_cut_failure, order_failure, nesting_failure,
passed. These are generic spherical controls, not zero-Count examples.
An exhaustive forest control checks the parity lemma before formalization.
"""

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_contour_mesh_gate import verify_archive
from v24_geodesic_mincut_gate import boundary_order, connected, validate_sphere
from v24_goldberg import consistently_oriented_face_cycles, edge_face_adjacency
from v24_thin_annulus_cut_gate import annulus


def bfs_tree(size, edges, root):
    adj = [[] for _ in range(size)]
    for e, (u, v) in edges.items():
        adj[u].append((v, e))
        adj[v].append((u, e))
    parent, depth, pedge = {root: root}, {root: 0}, {}
    order = [root]
    for u in order:
        for v, e in sorted(adj[u]):
            if v not in parent:
                parent[v], depth[v], pedge[v] = u, depth[u] + 1, e
                order.append(v)
    assert len(order) == size, "cotree_failure"
    return parent, depth, pedge, order


def ancestor_edges(v, parent, pedge):
    result = set()
    while parent[v] != v:
        result.add(pedge[v])
        v = parent[v]
    return result


def return_permutation(faces, side, cut, edges):
    phi = {}
    for cycle in faces:
        for i, u in enumerate(cycle):
            v, w = cycle[(i + 1) % len(cycle)], cycle[(i + 2) % len(cycle)]
            phi[u, v] = (v, w)
    edge_id = {tuple(sorted(e)): i for i, e in enumerate(edges)}
    result = {}
    for e in cut:
        u, v = edges[e]
        if u not in side:
            u, v = v, u
        # Start just after the inward boundary dart, and stop at the next
        # outward boundary dart of the same literal face.
        dart = phi[v, u]
        seen = set()
        while dart[1] in side:
            assert dart[0] in side and dart not in seen, "order_failure"
            seen.add(dart)
            dart = phi[dart]
        assert dart[0] in side, "order_failure"
        result[e] = edge_id[tuple(sorted(dart))]
    assert set(result.values()) == set(cut), "order_failure"
    return result


def inspect(graph):
    validate_sphere(graph)
    edges = [tuple(e) for e in graph["primal_edges"]]
    n, faces = graph["primal_vertex_count"], consistently_oriented_face_cycles(graph)
    ef = edge_face_adjacency(graph)
    F = len(faces)
    roots = sorted({0, F - 1, max(range(F), key=lambda f: len(faces[f]))})
    checks, chains, width, height = 0, 0, 0, 0
    rows = []
    for root in roots:
        dp, dd, de, _ = bfs_tree(F, ef, root)
        dual = set(de.values())
        primal = {e: uv for e, uv in enumerate(edges) if e not in dual}
        assert len(primal) == n - 1, "cotree_failure"
        pp, pd, pe, order = bfs_tree(n, primal, 0)
        sides = {u: {u} for u in order}
        for u in reversed(order[1:]):
            sides[pp[u]] |= sides[u]
        cuts, cyclic = {}, {}
        for u in order[1:]:
            side, other = sides[u], set(range(n)) - sides[u]
            cut = {e for e, (v, w) in enumerate(edges) if (v in side) != (w in side)}
            f, g = ef[pe[u]]
            cycle = ancestor_edges(f, dp, de) ^ ancestor_edges(g, dp, de) ^ {pe[u]}
            assert cut == cycle and cut & set(primal) == {pe[u]}, "full_cut_failure"
            assert len(cut) <= 2 * max(dd.values()) + 1, "full_cut_failure"
            assert connected(n, edges, side) and connected(n, edges, other), "cotree_failure"
            boundary_order(ef, sorted(cut))
            left = return_permutation(faces, side, cut, edges)
            right = return_permutation(faces, other, cut, edges)
            assert all(right[left[e]] == e for e in cut), "order_failure"
            inner = {e for e, (v, w) in enumerate(edges) if v in side and w in side}
            outer = {e for e, (v, w) in enumerate(edges) if v in other and w in other}
            assert 3 * len(side) == 2 * len(inner) + len(cut)
            assert 3 * len(other) == 2 * len(outer) + len(cut)
            incident = set(range(len(edges))) - outer
            middle = {v for e in incident for v in edges[e]} & {v for e in outer for v in edges[e]}
            assert len(middle) <= len(cut), "full_cut_failure"
            cyclic[u] = len(inner) >= len(side) and len(outer) >= len(other)
            if min(len(side), len(other)) >= len(cut) - 1:
                assert cyclic[u], "full_cut_failure"
            cuts[u] = incident
            checks += 1
            width = max(width, len(cut))
        tip = max(order, key=lambda u: pd[u])
        path = []
        while pp[tip] != tip:
            path.append(tip)
            tip = pp[tip]
        for u, v in zip(path, path[1:]):
            assert sides[u] < sides[v] and cuts[u] < cuts[v], "nesting_failure"
            chains += 1
        height = max(height, max(dd.values()))
        rows.append(dict(dual_root=root, dual_height=max(dd.values()),
                         primal_height=max(pd.values()), cyclic_chain=sum(cyclic[u] for u in path)))
    return dict(vertices=n, faces=F, cut_checks=checks, nesting_checks=chains,
                max_cut_width=width, max_dual_height=height, roots=rows)


def forest_control():
    checked, forests = 0, 0
    for n in range(6):
        possible = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            checked += 1
            parent = list(range(n))
            degree = Counter()

            def find(v):
                while parent[v] != v:
                    v = parent[v]
                return v

            selected = [e for i, e in enumerate(possible) if mask >> i & 1]
            for u, v in selected:
                x, y = find(u), find(v)
                if x == y:
                    break
                parent[x] = y
                degree.update((u, v))
            else:
                forests += 1
                assert not selected or any(d % 2 for d in degree.values()), "parity_failure"
    return dict(graphs=checked, forests=forests)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    archive = json.loads(Path("results/fourcolor/v24_contour_mesh_gate.json").read_text())
    verify_archive(archive)
    population = [dict(family=f"GP({r['frequency']},0)", **inspect(r["graph"]))
                  for r in archive["receipts"]]
    population += [dict(family=f"annulus({k},{L})", **inspect(annulus(k, L)[0]))
                   for L in range(1, 5) for k in (8, 16, 32, 64)]
    result = dict(schema="fourcolor-v24-tree-cotree-v1", population=population,
                  forest_control=forest_control(), outcome="passed")
    if args.verify_only:
        assert result == json.loads(args.verify_only.read_text()), "receipt_mismatch"
        print("tree-cotree full-cut replay passed")
    else:
        if args.output:
            atomic_write_json(args.output, result)
            print(dict(maps=len(population), cut_checks=sum(r["cut_checks"] for r in population),
                       nesting_checks=sum(r["nesting_checks"] for r in population),
                       forest_control=result["forest_control"], outcome=result["outcome"]))
        else:
            print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
