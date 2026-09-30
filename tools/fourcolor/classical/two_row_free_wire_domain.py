#!/usr/bin/env python3
"""Check the two-row theorem's geometric domain in the saved residual map.

This replay checks literal row rotations, both exterior shores, boundary
first returns and the retained wire slots. It reuses the saved colourings;
it does not repeat the occurrence census or certify a Lean occurrence theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import networkx as nx

from alternating_lobe_probe import data
from alternating_cycle_probe import cycles

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are replay checks.')


def replay(record):
    saved = json.loads(record.read_text())
    for relative, digest in saved['source_sha256'].items():
        assert hashlib.sha256((REPO / relative).read_bytes()).hexdigest() == digest
    example = saved['two_row_wiring_example']
    source = next(m for m in saved['maps'] if m['id'] == example['source_map'])
    graph, alpha, rho, old_faces = data(source['rotation'])
    rows, k = example['rows'], example['width']
    assert len(rows) == 2 and k >= 3
    deleted = set().union(*map(set, rows))
    assert len(deleted) == 4*k and all(len(row) == 2*k for row in rows)
    third = lambda v, row: next(u for u in graph[v] if u not in row)
    left = [third(rows[0][2*i], rows[0]) for i in range(k)]
    right = [third(rows[1][2*i+1], rows[1]) for i in range(k)]
    boundary = [(left[i], rows[0][2*i]) for i in range(k)] + [
        (right[i], rows[1][2*i+1]) for i in range(k)]
    assert len(set(boundary)) == 2*k
    for row in rows:
        assert graph.subgraph(row).number_of_edges() == 2*k
        for i in range(k):
            even, odd = row[2*i], row[2*i+1]
            even_star = [third(even, row), odd, row[(2*i-1) % (2*k)]]
            odd_star = [even, row[(2*i+2) % (2*k)], third(odd, row)]
            for v, star in ((even, even_star), (odd, odd_star)):
                assert set(star) == set(graph[v])
                assert all(rho[v, star[j]] == (v, star[(j+1) % 3]) for j in range(3))
    assert all(third(rows[0][2*i+1], rows[0]) == rows[1][2*i]
               and third(rows[1][2*i], rows[1]) == rows[0][2*i+1] for i in range(k))
    outside = set(graph) - deleted
    exterior = graph.subgraph(outside)
    components = list(nx.connected_components(exterior))
    assert len(components) == 2
    left_shore = next(s for s in components if left[0] in s)
    right_shore = next(s for s in components if right[0] in s)
    assert left_shore != right_shore
    assert set(left) <= left_shore and set(right) <= right_shore
    assert all((u in left_shore) == (v in left_shore) for u, v in exterior.edges())
    open_phi = {d: rho[d] if d[1] in deleted else rho[alpha[d]]
                for d in alpha if d[0] in outside}
    assert set(open_phi) == set(open_phi.values())
    boundary_index = {d: i for i, d in enumerate(boundary)}
    returns = []
    for d in boundary:
        nxt = open_phi[d]
        for _ in range(len(open_phi)):
            if nxt in boundary_index:
                returns.append(boundary_index[nxt])
                break
            nxt = open_phi[nxt]
        else:
            raise AssertionError('Boundary first return is missing')
    expected_return = [(i-1) % k for i in range(k)] + [k+(i+1) % k for i in range(k)]
    assert returns == expected_return
    redirects = {}
    for i in range(k):
        u, v = left[(i+1) % k], right[i]
        assert u != v
        redirects[u, rows[0][2*((i+1) % k)]] = v
        redirects[v, rows[1][2*i+1]] = u
    small, small_rho = nx.Graph(), {}
    for u in sorted(outside):
        v = min(graph[u])
        star = [v, rho[u, v][1], rho[rho[u, v]][1]]
        new_star = [redirects.get((u, v), v) for v in star]
        assert new_star == example['smaller_rotation'][str(u)]
        assert len(set(new_star)) == 3 and u not in new_star
        for j, v in enumerate(new_star):
            assert v in outside
            small.add_edge(u, v)
            small_rho[u, v] = (u, new_star[(j+1) % 3])
    assert all(d[::-1] in small_rho for d in small_rho)
    new_faces = cycles({d: small_rho[d[::-1]] for d in small_rho})
    open_faces = cycles(open_phi)
    assert nx.is_connected(small) and not list(nx.bridges(small))
    assert len(small) - small.number_of_edges() + len(new_faces) == 2
    assert len(new_faces) + 2 == len(open_faces) + k
    colours = {frozenset((u, v)): c+1 for u, v, c in example['smaller_colour_edges']}
    restored = {frozenset((u, v)): c for u, v, c in example['restored_colour_edges']}
    for current, assignment in ((small, colours), (graph, restored)):
        assert set(assignment) == {frozenset(e) for e in current.edges()}
        assert all({assignment[frozenset((u, v))] for v in current[u]} == {1, 2, 3}
                   for u in current)
    assert all(restored[frozenset(d)] == colours[frozenset((d[0], redirects.get(d, d[1])))]
               for d in alpha if d[0] in outside)
    return dict(evidence='Independent finite domain replay; not a Lean occurrence certificate.',
                source_map=source['id'], width=k, original_vertices=len(graph),
                smaller_vertices=len(small), vertices_removed=len(deleted),
                literal_row_rotation_steps_checked=12*k,
                connected_shore_sizes=[len(left_shore), len(right_shore)],
                boundary_ports_checked=2*k, opposite_first_return=returns,
                retained_exterior_vertices=True, retained_cyclic_slots=True,
                connected_cubic_bridgeless=True, whole_euler_preserved=True,
                open_exterior_faces=len(open_faces), original_faces=len(old_faces),
                smaller_faces=len(new_faces), all_exterior_dart_colours_retained=True,
                geometric_domain_holds=True, global_occurrence_coverage_proved=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE/'residual-coverage-probe.json')
    parser.add_argument('--output', type=Path, default=HERE/'two-row-free-wire-domain.json')
    args = parser.parse_args()
    assert args.output.resolve() not in (args.input.resolve(), Path(__file__).resolve())
    result = replay(args.input)
    result['input_sha256'] = hashlib.sha256(args.input.read_bytes()).hexdigest()
    result['program_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('width', 'vertices_removed',
          'connected_shore_sizes', 'literal_row_rotation_steps_checked', 'geometric_domain_holds')}))


if __name__ == '__main__':
    main()
