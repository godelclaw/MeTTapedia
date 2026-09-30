#!/usr/bin/env python3
"""Replay the residual of the current diamond/tube/cap occurrence union.

Explicit rotations check all rooted face predicates and all alternating
dart-phase orbits. A two-row shifted wiring is checked separately, including
a complete smaller colouring and reconstruction of every original edge.
These are finite program checks, not kernel certificates or global coverage.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys

import networkx as nx

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
sys.path.insert(0, str(HERE))
from alternating_lobe_probe import data, tait_colouring
from alternating_cycle_probe import alternating_orbits, oriented_row, grow, cycles
from hexagonal_collar_probe import graph_rotation
from diamond_supply_probe import control
from padded_cap_recognition_probe import recognize
from twisted_tube_probe import ring_colours, complementary

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are replay checks.')


def serial(graph, rho):
    rows = []
    for u in sorted(graph):
        v = min(graph[u])
        rows.append(','.join(map(str, (v, rho[u, v][1], rho[rho[u, v]][1]))))
    return ';'.join(rows)


def dual_truncate(raw):
    graph, alpha, rho, faces = data(raw['rotation'])
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    edges = set()
    vertices = {(i, face_of[alpha[d]]) for i, face in enumerate(faces) for d in face}
    ids = {v: i for i, v in enumerate(sorted(vertices))}
    assert len(ids) == 3 * len(graph)
    for i, face in enumerate(faces):
        adjacent = [face_of[alpha[d]] for d in face]
        assert len(set(adjacent)) == len(face)
        for j, v in enumerate(adjacent):
            a, b, c = ids[i, v], ids[i, adjacent[(j+1) % len(face)]], ids[v, i]
            edges.add(tuple(sorted((a, b))))
            edges.add(tuple(sorted((a, c))))
    small, _, new_rho = graph_rotation(sorted(edges))
    assert len(small) == 3 * len(graph)
    rotation = serial(small, new_rho)
    data(rotation)
    return dict(id='dual-truncate-' + raw['id'], rotation=rotation,
                input_id=raw['id'], input_rotation_sha256=hashlib.sha256(raw['rotation'].encode()).hexdigest())


def inspect(raw):
    graph, alpha, rho, faces = data(raw['rotation'])
    face_of = {d: face for face in faces for d in face}
    length = lambda d: len(face_of[d])
    diamonds = [d for d in alpha if length(rho[rho[d]]) == length(rho[rho[alpha[d]]]) == 5]
    caps = []
    for face in faces:
        for root in face:
            result = recognize(len(face), root, graph, {d: d[0] for d in alpha}, alpha, rho, faces)
            if result and all(result[k] for k in ('distinct_vertices', 'boundary_short_faces',
                                                 'exposed_ports', 'exterior_connected')):
                caps.append(dict(root=root, **result))
    orbits = alternating_orbits(alpha, rho)
    rows, failures = [], []
    nonsimple = 0
    for orbit in orbits:
        vs = [d[0] for d, _ in orbit]
        if len(set(vs)) != len(vs):
            nonsimple += 1
            continue
        if graph.subgraph(vs).number_of_edges() != len(vs):
            failures.append(dict(kind='noninduced simple orbit', vertices=vs))
            continue
        row = oriented_row(graph, rho, orbit)
        assert row is not None
        history = grow(graph, alpha, rho, face_of, row)
        rows.append(history)
    tubes = [h for h in rows if len(h['rows']) >= 3]
    assert len(orbits) == nonsimple + len(rows) + len(failures)
    return dict(id=raw['id'], vertices=len(graph), edges=graph.number_of_edges(),
                face_lengths=dict(sorted(Counter(map(len, faces)).items())),
                rotation_sha256=hashlib.sha256(raw['rotation'].encode()).hexdigest(),
                flanked_darts=len(diamonds), cap_rooted_occurrences=len(caps),
                alternating_orbits=len(orbits), nonsimple_orbits=nonsimple,
                simple_orbit_rejections=failures,
                complete_rows=len(rows), qualifying_tube_starts=len(tubes),
                row_width_histogram=dict(sorted(Counter(h['width'] for h in rows).items())),
                extension_histogram=dict(sorted(Counter(h['successful_extensions'] for h in rows).items())),
                covered_by_occurrence_union=bool(diamonds or caps or tubes),
                smallest_cap=caps[0] if caps else None,
                longest_tube=max(tubes, key=lambda h: h['successful_extensions'], default=None))


def short_cycles(raw):
    """Check every simple dual circuit of length at most five.

    This is a finite diagnostic of dual circuits, not a Lean proof of the
    universal cyclic-cut or minimal-counterexample hypotheses.
    """
    graph, alpha, _, faces = data(raw['rotation'])
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    pair_edge = {}
    for d in alpha:
        if d < alpha[d]:
            pair = tuple(sorted((face_of[d], face_of[alpha[d]])))
            assert pair[0] != pair[1] and pair not in pair_edge
            pair_edge[pair] = d
    dual = nx.Graph(list(pair_edge))
    circuits = []

    def visit(path):
        for v in sorted(dual[path[-1]]):
            if v == path[0] and len(path) >= 3 and path[1] < path[-1]:
                circuits.append(path)
            elif v > path[0] and v not in path and len(path) < 5:
                visit(path + [v])

    for v in sorted(dual):
        visit([v])
    assert len(circuits) == len(set(map(tuple, circuits)))
    hist, cyclic, violations = Counter(), Counter(), []
    for cycle in circuits:
        cut = [pair_edge[tuple(sorted((cycle[i], cycle[(i+1) % len(cycle)])))]
               for i in range(len(cycle))]
        remaining = graph.copy()
        remaining.remove_edges_from(cut)
        shores = list(nx.connected_components(remaining))
        assert len(shores) == 2
        hist[len(cycle)] += 1
        if all(remaining.subgraph(s).number_of_edges() >= len(s) for s in shores):
            cyclic[len(cycle)] += 1
            if len(cycle) <= 4 or min(map(len, shores)) > 5:
                violations.append(dict(dual_cycle=cycle, primal_cut=cut,
                                       shore_sizes=sorted(map(len, shores))))
    assert not violations
    return dict(scope='All simple dual circuits of length three, four or five.',
                circuits_by_length=dict(sorted(hist.items())),
                cyclic_circuits_by_length=dict(sorted(cyclic.items())),
                nontrivial_small_cyclic_circuit_violations=violations,
                universal_cut_domain_kernel_certified=False,
                minimal_counterexample_status_inferred=False)


def first_ring(x):
    """Find a cyclic first ring through its three possible cursor values."""
    k = len(x)
    for initial in (1, 2, 3):
        @lru_cache(None)
        def search(i, previous):
            if i == k:
                return ((), ()) if previous == initial else None
            a = x[i] ^ previous
            if a == 0:
                return None
            for b in (1, 2, 3):
                if b != a:
                    tail = search(i+1, b)
                    if tail is not None:
                        return ((a,) + tail[0], (b,) + tail[1])
            return None
        result = search(0, initial)
        if result is not None:
            assert ring_colours(*result)[0] == x
            return result
    raise AssertionError('No first ring found for the nonzero input word')


def reconstruct_example(raw):
    graph, alpha, rho, faces = data(raw['rotation'])
    face_of = {d: face for face in faces for d in face}
    histories = []
    for orbit in alternating_orbits(alpha, rho):
        row = oriented_row(graph, rho, orbit)
        if row is not None:
            histories.append(grow(graph, alpha, rho, face_of, row))
    history = max(histories, key=lambda h: h['successful_extensions'])
    rows = list(map(tuple, history['rows']))
    k = history['width']
    assert len(rows) == 2 and k == 18
    third = lambda v, row: next(u for u in graph[v] if u not in row)
    left = [third(rows[0][2*i], rows[0]) for i in range(k)]
    right = [third(rows[1][2*i+1], rows[1]) for i in range(k)]
    deleted = set().union(*map(set, rows))
    redirects = {}
    for i in range(k):
        u, v = left[(i+1) % k], right[i]
        redirects[u, rows[0][2*((i+1) % k)]] = v
        redirects[v, rows[1][2*i+1]] = u
    assert len(redirects) == 2*k
    new_rotation = {}
    for u in sorted(graph):
        if u in deleted:
            continue
        v = min(graph[u])
        star = (v, rho[u, v][1], rho[rho[u, v]][1])
        new_rotation[u] = [redirects.get((u, v), v) for v in star]
        assert len(set(new_rotation[u])) == 3 and u not in new_rotation[u]
    small, small_rho = nx.Graph(), {}
    for u, star in new_rotation.items():
        for j, v in enumerate(star):
            assert v not in deleted and u in new_rotation[v]
            small.add_edge(u, v)
            small_rho[u, v] = (u, star[(j+1) % 3])
    small_faces = cycles({d: small_rho[d[::-1]] for d in small_rho})
    assert nx.is_connected(small) and not list(nx.bridges(small))
    assert len(small)-small.number_of_edges()+len(small_faces) == 2
    assert len(graph)-len(small) == 4*k == 72
    small_colours = tait_colouring(small)
    colours = {frozenset((u, v)): c+1 for u, v, c in small_colours}
    assert all({colours[frozenset((u, v))] for v in small[u]} == {1, 2, 3}
               for u in small)
    x = tuple(colours[frozenset((left[i], right[(i-1) % k]))] for i in range(k))
    y = tuple(colours[frozenset((right[i], left[(i+1) % k]))] for i in range(k))
    assert y == x[1:] + x[:1]
    a, b = first_ring(x)
    second, _ = complementary(a, b)
    assert ring_colours(*second)[1] == y
    restored = {frozenset((u, v)): colours[frozenset((u, v))]
                for u, v in graph.edges() if u not in deleted and v not in deleted}
    for i in range(k):
        restored[frozenset((left[i], rows[0][2*i]))] = x[i]
    for j, (aa, bb) in enumerate(((a, b), second)):
        rr = rows[j]
        _, yy = ring_colours(aa, bb)
        for i in range(k):
            restored[frozenset((rr[2*i], rr[2*i+1]))] = aa[i]
            restored[frozenset((rr[2*i+1], rr[(2*i+2) % (2*k)]))] = bb[i]
            target = rows[1][2*i] if j == 0 else right[i]
            restored[frozenset((rr[2*i+1], target))] = yy[i]
    assert set(restored) == {frozenset(e) for e in graph.edges()}
    assert all({restored[frozenset((u, v))] for v in graph[u]} == {1, 2, 3}
               for u in graph)
    for u, v in alpha:
        if u not in deleted:
            assert restored[frozenset((u, v))] == colours[frozenset((u, redirects.get((u, v), v)))]
    return dict(evidence='Independent finite geometry and genuine colouring reconstruction.',
                source_map=raw['id'], original_vertices=len(graph), smaller_vertices=len(small),
                rows=rows, width=k, vertices_removed=4*k,
                exterior_components=nx.number_connected_components(graph.subgraph(set(graph)-deleted)),
                shift=1, connected_cubic_bridgeless=True, spherical_euler=2,
                smaller_face_lengths=dict(sorted(Counter(map(len, small_faces)).items())),
                smaller_rotation=new_rotation, smaller_colour_edges=small_colours,
                left_word=x, right_word=y, first_ring=(a, b), second_ring=second,
                restored_colour_edges=[[*sorted(e), c] for e, c in
                    sorted(restored.items(), key=lambda ec: sorted(ec[0]))],
                all_exterior_darts_preserved=True,
                uniform_replacement_geometry_kernel_certified=False)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE/'residual-coverage-probe.json')
    args = parser.parse_args()
    assert args.output.resolve() != Path(__file__).resolve()
    results = []
    for frequency in (1, 2, 3, 4):
        raw = control(frequency)
        for candidate in (raw, dual_truncate(raw)):
            result = inspect(candidate)
            result['rotation'] = candidate['rotation']
            results.append(result)
            print(json.dumps({k: result[k] for k in ('id', 'vertices', 'flanked_darts',
                 'cap_rooted_occurrences', 'alternating_orbits', 'nonsimple_orbits',
                 'qualifying_tube_starts', 'covered_by_occurrence_union')}), flush=True)
    residual = next(r for r in results if not r['covered_by_occurrence_union'])
    assert residual['vertices'] == 240 and not residual['simple_orbit_rejections']
    report = dict(evidence='Independent finite program evidence, not Lean certificates.',
                  status='A verified finite source is outside the present occurrence union; a shifted two-row replacement and full colouring reconstruction succeed in that example.',
                  candidate='The three currently recognized occurrence families cover every fullerene.',
                  candidate_holds_in_checked_sources=False,
                  minimality_dependent_coverage_refuted=False,
                  maps=results,
                  residual_map=residual['id'],
                  short_dual_cycle_diagnostics=short_cycles(residual),
                  two_row_wiring_example=reconstruct_example(residual),
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  source_sha256={str(p.relative_to(REPO)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in [Path(__file__), HERE/'alternating_lobe_probe.py',
                    HERE/'alternating_cycle_probe.py', HERE/'diamond_supply_probe.py',
                    HERE/'hexagonal_collar_probe.py', HERE/'padded_cap_recognition_probe.py',
                    HERE/'padded_cap_geometry_probe.py', HERE/'padded_cap_probe.py',
                    HERE/'twisted_tube_probe.py', HERE/'hexagonal_seam_probe.py',
                    HERE.parent/'v24_goldberg.py', HERE.parent/'v24_annular_census.py']})
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
