#!/usr/bin/env python3
"""Test cyclic order on persistent edges of complete nested planar bonds.

Preregistered claim: restricting each side's capped facial successor to
the common crossing edges gives the same permutation under literal edge
identity. Test every nested pair of cyclic, connected, coconnected sides
of small prisms, and cap-containing sides of a thin annulus. At least one
strict pair must have three persistent wires; inverse-order mutations
must be detected there. This is a geometry gate, not a colouring census
or a configuration catalogue. Outcomes: invalid_geometry, order_failure,
insufficient_controls, passed.
"""

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_geodesic_mincut_gate import connected, validate_sphere
from v24_goldberg import consistently_oriented_face_cycles
from v24_thin_annulus_cut_gate import annulus
from v24_tree_cotree_gate import return_permutation


def induced(p, keep):
    result = {}
    for x in sorted(keep):
        y = p[x]
        seen = set()
        while y not in keep:
            assert y not in seen, "invalid_geometry"
            seen.add(y)
            y = p[y]
        result[x] = y
    return result


def single_cycle(p):
    if not p:
        return False
    x = min(p)
    seen = set()
    while x not in seen:
        seen.add(x)
        x = p[x]
    return x == min(p) and seen == set(p)


def components(p, edges):
    labels = {x: x for x in p}
    for a, b in list(p.items()) + list(edges):
        old, new = labels[b], labels[a]
        labels = {x: new if c == old else c for x, c in labels.items()}
    return labels


def face_perm(p, edges):
    alpha = dict((x, x) for x in p)
    for a, b in reversed(edges):
        alpha = {x: b if y == a else a if y == b else y for x, y in alpha.items()}
    return {x: p[y] for x, y in alpha.items()}


def matchings(points):
    if not points:
        yield []
        return
    a, *tail = points
    yield from matchings(tail)
    for b in tail:
        for rest in matchings([x for x in tail if x != b]):
            yield [(a, b)] + rest


def euler_gate():
    checked, nonplanar_rejections, specimen = 0, 0, None
    for n in range(1, 6):
        subsets = [{i for i in range(n) if mask >> i & 1} for mask in range(1, 1 << n)]
        for values in itertools.permutations(range(n)):
            rho = dict(enumerate(values))
            V = len(set(components(rho, []).values()))
            for edges in matchings(list(range(n))):
                p = face_perm(rho, edges)
                F = len(set(components(p, []).values()))
                C = len(set(components(rho, edges).values()))
                assert V + F <= len(edges) + 2 * C
                plane = V + F == len(edges) + 2 * C
                for mask in range(1 << len(edges)):
                    base = [e for i, e in enumerate(edges) if mask >> i & 1]
                    q = face_perm(rho, base)
                    comp = components(rho, base)
                    if plane:
                        assert V + len(set(components(q, []).values())) == len(base) + 2 * len(set(comp.values()))
                    for hit in subsets:
                        if len({comp[x] for x in hit}) != 1 or not single_cycle(induced(p, hit)):
                            continue
                        same = induced(p, hit) == induced(q, hit)
                        if plane:
                            assert same, "order_failure"
                            checked += 1
                        elif not same:
                            nonplanar_rejections += 1
                            if specimen is None:
                                specimen = dict(rotation=values, edges=edges, base=base,
                                                marks=sorted(hit), euler=V-len(edges)+F,
                                                final_order=sorted(induced(p, hit).items()),
                                                base_order=sorted(induced(q, hit).items()))
    assert nonplanar_rejections, "insufficient_controls"
    return dict(plane_restrictions=checked, nonplanar_rejections=nonplanar_rejections,
                nonplanar_specimen=specimen)


def prism(k):
    edges = [(i, (i + 1) % k) for i in range(k)]
    edges += [(k + i, k + (i + 1) % k) for i in range(k)]
    edges += [(i, k + i) for i in range(k)]
    faces = [list(range(k)), list(range(k, 2 * k))]
    faces += [[i, (i + 1) % k, k + (i + 1) % k, k + i] for i in range(k)]
    return dict(primal_vertex_count=2 * k,
                primal_edges=[tuple(sorted(e)) for e in edges], face_cycles=faces)


def check_graph(name, graph, candidates):
    validate_sphere(graph)
    n, edges = graph["primal_vertex_count"], graph["primal_edges"]
    faces = consistently_oriented_face_cycles(graph)
    universe = set(range(n))
    sides = []
    for A in candidates:
        Ac = universe - A
        if not connected(n, edges, A) or not connected(n, edges, Ac):
            continue
        if sum(u in A and v in A for u, v in edges) < len(A):
            continue
        if sum(u in Ac and v in Ac for u, v in edges) < len(Ac):
            continue
        cut = {e for e, (u, v) in enumerate(edges) if (u in A) != (v in A)}
        p = return_permutation(faces, A, cut, edges)
        q = return_permutation(faces, Ac, cut, edges)
        assert single_cycle(p) and all(q[p[e]] == e for e in cut), "invalid_geometry"
        sides.append((A, cut, p))
    hist, reversals, witness = Counter(), 0, None
    for A, ca, pa in sides:
        for B, cb, pb in sides:
            if not A < B:
                continue
            common = ca & cb
            assert all((edges[e][0] in A) == (edges[e][0] in B) for e in common)
            pi, po = induced(pa, common), induced(pb, common)
            assert pi == po, ("order_failure", name, sorted(A), sorted(B), pi, po)
            hist[len(common)] += 1
            if len(common) >= 3:
                inverse = {v: u for u, v in po.items()}
                assert pi != inverse, "insufficient_controls"
                reversals += 1
                if witness is None or len(common) > len(witness["common_edges"]):
                    witness = dict(inner=sorted(A), outer=sorted(B),
                                   inner_width=len(ca), outer_width=len(cb),
                                   common_edges=sorted(common),
                                   inner_successor=sorted(pa.items()),
                                   outer_successor=sorted(pb.items()),
                                   common_successor=sorted(pi.items()))
    return dict(family=name, vertices=n, cyclic_sides=len(sides),
                strict_pairs_by_common_width=sorted(hist.items()),
                rejected_reversals=reversals, witness=witness)


def audit():
    rows = []
    for k in (3, 4, 5, 6):
        rows.append(check_graph(f"prism({k})", prism(k),
                    ({i for i in range(2 * k) if mask >> i & 1}
                     for mask in range(1 << (2 * k)))))
    # All middle-band assignments between two fixed cap cycles. Thus lateral
    # attachments, not just a chosen sweep, participate in the test.
    k = 6
    graph, _, _, _ = annulus(k, 1)
    cap = {4 * i for i in range(k)}
    middle = [4 * i + r for i in range(k) for r in (1, 2)]
    rows.append(check_graph("annulus(6,1)", graph,
                (cap | {v for i, v in enumerate(middle) if mask >> i & 1}
                 for mask in range(1 << len(middle)))))
    assert sum(r["rejected_reversals"] for r in rows) > 0, "insufficient_controls"
    # Generic surgery gate: if the marked points stay on one cycle before
    # and after a transposition, their first-return order is unchanged.
    # This includes both splitting a face and merging two faces.
    surgeries, restrictions = 0, 0
    for n in range(1, 6):
        subsets = [{i for i in range(n) if mask >> i & 1} for mask in range(1 << n)]
        for values in itertools.permutations(range(n)):
            p = dict(enumerate(values))
            for a, b in itertools.combinations(range(n), 2):
                q = {x: b if y == a else a if y == b else y for x, y in p.items()}
                for hit in subsets:
                    pi, qi = induced(p, hit), induced(q, hit)
                    if single_cycle(pi) and single_cycle(qi):
                        assert pi == qi, "order_failure"
                        surgeries += 1
            if n <= 4:
                for big in subsets:
                    for small in subsets:
                        if small <= big:
                            assert induced(induced(p, big), small) == induced(p, small)
                            restrictions += 1
    return json.loads(json.dumps(dict(schema="fourcolor-v24-persistent-wire-order-v1",
                                    outcome="passed", cases=rows,
                                    permutation_surgeries=surgeries,
                                    nested_restrictions=restrictions,
                                    euler=euler_gate())))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-only", type=Path)
    args = parser.parse_args()
    result = audit()
    if args.output:
        atomic_write_json(args.output, result)
    if args.verify_only:
        assert result == json.loads(args.verify_only.read_text()), "receipt_mismatch"
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
