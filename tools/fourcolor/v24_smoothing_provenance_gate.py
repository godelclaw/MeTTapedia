#!/usr/bin/env python3
"""Actual smoothing provenance, trapped Kempe orbits, and matching escape.

P1 asks whether some smaller colouring has the lifting cycle.
P2 asks whether every smaller Kempe orbit meets those colourings.
P3 asks whether every smaller colouring already has the cycle.
The fixed normal-form control refutes P2 and P3, not P1.

A second construction searches graph-supported perfect matchings differing
from one colour class on a single alternating cycle. It verifies both
all-even residual cycles and joining of the marked edges before actually
lifting a colouring. No universal exchange-existence claim is made.
This is a closed-graph proof-method gate, not a patch catalogue.
"""
import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
from pathlib import Path
import subprocess

from v24_absolute_topology_gate import enumerated, girth
from v24_annular_census import atomic_write_json
from v24_deletion_orbit_gate import incidence, orbits
from v24_facial_bond_gate import validate
from v24_goldberg import consistently_oriented_face_cycles, edge_face_adjacency
from v24_geodesic_mincut_gate import connected
from v24_plantri_seed_audit import graph_record, parse_ascii_graph
from v24_smoothing_cycle_gate import (check_geometry, common_cycles,
    perfect_matchings, complement_cycles)

ASCII = '30 bcd,aef,agh,aij,bjk,blg,cfm,cni,dho,dpe,eqr,frs,gst,htu,iuv,jvq,kpw,kxl,lym,mzn,n{o,o|p,q}x,rwy,sx~,t~{,uz|,v{},w|~,y}z'


def smooth(graph, removed):
    n, edges = graph['primal_vertex_count'], list(map(tuple, graph['primal_edges']))
    u, v = edges[removed]
    inc = incidence(n, edges)
    neighbors = [sorted({w for e in inc[x] for w in edges[e]} - {x}) for x in range(n)]
    pairs = [tuple(x for x in neighbors[z] if x not in (u, v)) for z in (u, v)]
    assert len(set(sum((list(p) for p in pairs), []))) == 4
    live = sorted(set(range(n)) - {u, v})
    ren = {x: i for i, x in enumerate(live)}
    old_ids = [i for i, e in enumerate(edges) if not set(e) & {u, v}]
    raw = sorted([edges[i] for i in old_ids] + [tuple(sorted(p)) for p in pairs])
    assert len(set(raw)) == len(raw)
    successor = {}
    for face in consistently_oriented_face_cycles(graph):
        for i, x in enumerate(face):
            successor[x, face[i - 1]] = face[(i + 1) % len(face)]
    rows = []
    for x in live:
        a = neighbors[x][0]
        row = [a, successor[x, a], successor[x, successor[x, a]]]
        for z, (a, b) in zip((u, v), pairs):
            row = [b if y == z and x == a else a if y == z and x == b else y for y in row]
        rows.append([ren[y] for y in row])
    smaller = graph_record(rows, 0)
    validate(smaller, 2)
    assert smaller['primal_edges'] == [(ren[a], ren[b]) for a, b in raw]
    assert connected(n-2, smaller['primal_edges'], set(range(n-2)))
    assert all(connected(n-2, smaller['primal_edges'][:i] + smaller['primal_edges'][i+1:],
                         set(range(n-2))) for i in range(len(raw)))
    images = {i: raw.index(edges[i]) for i in old_ids}
    marks = [raw.index(tuple(sorted(p))) for p in pairs]
    faces = edge_face_adjacency(smaller)
    assert set(faces[marks[0]]) & set(faces[marks[1]])
    return smaller, images, marks, (u, v)


def lift(graph, smaller, images, marks, deleted, coloring, cycle):
    """Actually colour the expanded even cycle; no SAT solver in the lift."""
    pair, part = cycle
    n, edges = graph['primal_vertex_count'], graph['primal_edges']
    inc = incidence(n, edges)
    u, v = deleted
    middle = edges.index((min(u, v), max(u, v)))
    out = [-1] * len(edges)
    for i, j in images.items():
        out[i] = coloring[j]
    out[middle] = next(c for c in range(3) if c not in pair)
    expanded = {i for i, j in images.items() if j in part}
    expanded |= set(inc[u] + inc[v]) - {middle}
    assert len(expanded) == len(part) + 2 and len(expanded) % 2 == 0
    first = min(expanded)
    start, vertex = edges[first]
    edge, color, seen = first, pair[0], set()
    while edge not in seen:
        seen.add(edge)
        out[edge] = color
        nxt = (set(inc[vertex]) & expanded) - {edge}
        assert len(nxt) == 1
        edge = nxt.pop()
        vertex = next(x for x in edges[edge] if x != vertex)
        color = pair[0] + pair[1] - color
    assert edge == first and seen == expanded
    assert all(len({out[i] for i in row}) == 3 for row in inc)
    assert all(out[i] == coloring[j] for i, j in images.items() if j not in part)
    return out

def try_exchange(n, es, marks, coloring, targets):
    for omitted in range(3):
        before = frozenset(i for i, c in enumerate(coloring) if c == omitted)
        if set(marks) & before:
            continue
        for after, cycles in targets:
            delta = before ^ after
            if not delta:
                continue
            vertices = {v for i in delta for v in es[i]}
            if not connected(n, [es[i] for i in delta], vertices):
                continue
            # The symmetric difference of perfect matchings is 2-regular.
            assert all(sum(v in es[i] for i in delta) == 2 for v in vertices)
            out = [2 if i in after else -1 for i in range(len(es))]
            inc = incidence(n, es)
            for cycle in cycles:
                first = min(cycle)
                edge, vertex, color, seen = first, es[first][1], 0, set()
                while edge not in seen:
                    seen.add(edge)
                    out[edge] = color
                    edge = next(i for i in inc[vertex] if i in cycle and i != edge)
                    vertex = next(v for v in es[edge] if v != vertex)
                    color = 1 - color
                assert edge == first and seen == set(cycle) and color == 0
            assert all(len({out[i] for i in row}) == 3 for row in inc)
            assert common_cycles(n, es, out, marks)
            return dict(omitted=omitted, before=sorted(before), after=sorted(after),
                        carrier=sorted(delta), cycles=cycles, coloring=out)
    return None


def normal_geometry(graph):
    """Check the source-side geometric conditions, independently of plantri."""
    check_geometry(graph)
    n, edges = graph['primal_vertex_count'], graph['primal_edges']
    assert girth(n, edges) == 5
    dual = [tuple(fs) for fs in edge_face_adjacency(graph).values()]
    size = len(graph['face_cycles'])
    assert all(a != b for a, b in dual)
    assert len(set(tuple(sorted(e)) for e in dual)) == len(dual)
    tested = 0
    for k in range(5):
        for deleted in combinations(range(size), k):
            assert connected(size, dual, set(range(size)) - set(deleted))
            tested += 1
    return dict(girth=5, dual_vertices=size, dual_deletion_checks=tested,
                dual_vertex_connectivity_at_least=5)


def matching_targets(n, edges, marks):
    records, targets = [], []
    for matching in perfect_matchings(n, edges):
        cycles = complement_cycles(n, edges, matching)
        oddness = sum(len(c) % 2 for c in cycles)
        joined = any(set(marks) <= set(c) for c in cycles)
        records.append((matching, cycles, oddness, joined))
        if oddness == 0 and joined:
            targets.append((matching, cycles))
    return records, targets


def run():
    graph = graph_record(parse_ascii_graph(ASCII), 0)
    geometry = normal_geometry(graph)
    smaller, images, marks, deleted = smooth(graph, 0)
    edges = smaller['primal_edges']
    states = enumerated(28, edges)
    assert len(states) == 192 and marks == [0, 5]
    classes = orbits(28, edges, states)
    class_counts = [(len(o), sum(bool(common_cycles(28, edges, c, marks)) for c in o))
                    for o in classes]
    assert class_counts == [(6, 6), (36, 0), (6, 6), (144, 72)]
    bad = classes[1]
    records, targets = matching_targets(28, edges, marks)
    counts = Counter((oddness, joined) for _, _, oddness, joined in records)
    assert counts == {(0, False):45, (0, True):12, (2, False):30, (2, True):15}
    witnesses = [try_exchange(28, edges, marks, c, targets) for c in bad]
    assert all(w is not None for w in witnesses)
    upstairs = enumerated(30, graph['primal_edges'])
    assert len(upstairs) == 96
    for witness in witnesses:
        c = witness['coloring']
        lifted = lift(graph, smaller, images, marks, deleted, c,
                      common_cycles(28, edges, c, marks)[0])
        assert bytes(lifted) in upstairs
        assert bytes(c) not in bad
    witness = witnesses[0]
    # Negative control for the proposed parity step: a supported single-cycle
    # exchange can join the marks while creating two odd residual cycles.
    before = frozenset(witness['before'])
    unsafe = None
    for after, cycles, oddness, joined in records:
        delta = before ^ after
        verts = {v for i in delta for v in edges[i]}
        if oddness and joined and delta and connected(28, [edges[i] for i in delta], verts):
            unsafe = dict(after=sorted(after), carrier=sorted(delta),
                          cycles=cycles, oddness=oddness)
            break
    assert unsafe is not None
    return dict(schema='fourcolor-v24-smoothing-provenance-v1', graph=graph,
        geometry=geometry, removed_edge=0, smaller=smaller, marks=marks,
        smaller_girth=girth(28, edges), smaller_colorings=len(states),
        orbit_counts=[dict(size=a, usable=b) for a, b in class_counts],
        bad_seed=list(bad[0]), bad_orbit_size=len(bad),
        matching_counts=[dict(oddness=o, joined=j, count=num)
                         for (o,j),num in sorted(counts.items())],
        exchange_witness=witness, parity_failure=unsafe,
        successful_bad_orbit_exchanges=len(witnesses),
        original_colorings=len(upstairs),
        lifted_witness=lift(graph, smaller, images, marks, deleted, witness['coloring'],
                            common_cycles(28, edges, witness['coloring'], marks)[0]),
        scope='finite constructor/exhaustion check, not a Lean seal or a universal reduction theorem')


def census(plantri, largest):
    result = dict(flags=['-a', '-d', '-m5', '-c5'],
                  generator_sha256=hashlib.sha256(plantri.read_bytes()).hexdigest(),
                  population=[])
    for n in range(20, largest + 1, 2):
        data = subprocess.run([str(plantri), *result['flags'], str(n//2+2)],
                              capture_output=True, check=True).stdout
        lines = [x for x in data.decode('latin1').split('\n') if x.strip()]
        row = Counter(vertices=n, graphs=len(lines))
        for gi, line in enumerate(lines):
            graph = graph_record(parse_ascii_graph(line), gi)
            normal_geometry(graph)
            for removed in range(len(graph['primal_edges'])):
                smaller, images, marks, deleted = smooth(graph, removed)
                edges = smaller['primal_edges']
                states = enumerated(n-2, edges)
                assert states
                good = {c: common_cycles(n-2, edges, c, marks) for c in states}
                row['smoothings'] += 1
                row['colorings'] += len(states)
                row['pointwise_failures'] += sum(not v for v in good.values())
                if not any(good.values()):
                    result['existential_failure'] = dict(graph=graph, removed=removed,
                                                        smaller=smaller, marks=marks)
                    result['population'].append(dict(row))
                    return result
                for c, cycles in good.items():
                    if cycles:
                        lift(graph, smaller, images, marks, deleted, c, cycles[0])
                        row['constructed_lifts'] += 1
                targets = None
                for orbit in orbits(n-2, edges, states):
                    row['orbits'] += 1
                    if any(good[c] for c in orbit):
                        continue
                    row['orbit_failures'] += 1
                    if targets is None:
                        _, targets = matching_targets(n-2, edges, marks)
                    for c in orbit:
                        row['exchange_tests'] += 1
                        witness = try_exchange(n-2, edges, marks, c, targets)
                        if witness is None:
                            row['exchange_failures'] += 1
                        else:
                            c2 = witness['coloring']
                            lift(graph, smaller, images, marks, deleted, c2,
                                 common_cycles(n-2, edges, c2, marks)[0])
                            row['exchange_lifts'] += 1
                            row['max_exchange_carrier'] = max(row['max_exchange_carrier'],
                                                            len(witness['carrier']))
        row = dict(row, embeddings_sha256=hashlib.sha256(data).hexdigest())
        result['population'].append(row)
        print(json.dumps(row, sort_keys=True), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--plantri', type=Path)
    parser.add_argument('--largest', type=int, default=30)
    args = parser.parse_args()
    result = run()
    if args.plantri:
        result['census'] = census(args.plantri, args.largest)
    if args.output:
        atomic_write_json(args.output, result)
    print(json.dumps(dict(colorings=result['smaller_colorings'],
        orbits=result['orbit_counts'], exchanged=result['successful_bad_orbit_exchanges'],
        original_colorings=result['original_colorings']), sort_keys=True))


if __name__ == '__main__':
    main()
