#!/usr/bin/env python3
"""Replay the short-end-face implication on the stored two-row residual.

Check the literal row rotations, three tube steps, exterior first-return
arcs and their two components. This does not certify a Lean occurrence or
repeat the full occurrence census or any colouring search.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

import networkx as nx

from alternating_lobe_probe import data
from alternating_cycle_probe import alternating_orbits, oriented_row, grow

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are replay checks.')


def replay(record):
    saved = json.loads(record.read_text())
    for relative, digest in saved['source_sha256'].items():
        assert hashlib.sha256((REPO / relative).read_bytes()).hexdigest() == digest
    source = next(m for m in saved['maps']
                  if m['id'] == saved['two_row_wiring_example']['source_map'])
    graph, alpha, rho, faces = data(source['rotation'])
    face_of = {d: face for face in faces for d in face}
    phi = {d: rho[alpha[d]] for d in alpha}
    cases, lengths, rotation_steps, widths = [], Counter(), 0, Counter()
    for orbit in alternating_orbits(alpha, rho):
        row = oriented_row(graph, rho, orbit)
        if row is None:
            continue
        history = grow(graph, alpha, rho, face_of, row)
        if len(history['rows']) != 2:
            continue
        rows, k = history['rows'], history['width']
        third = lambda v, row: next(u for u in graph[v] if u not in row)
        deleted = set().union(*map(set, rows))
        assert len(deleted) == 4*k and k >= 3
        for row in rows:
            assert graph.subgraph(row).number_of_edges() == 2*k
            for i in range(k):
                even, odd = row[2*i], row[2*i+1]
                for v, star in ((even, (third(even, row), odd, row[(2*i-1) % (2*k)])),
                                (odd, (even, row[(2*i+2) % (2*k)], third(odd, row)))):
                    assert all(rho[v, star[j]] == (v, star[(j+1) % 3]) for j in range(3))
                    rotation_steps += 3
        assert all(third(rows[0][2*i+1], rows[0]) == rows[1][2*i]
                   and third(rows[1][2*i], rows[1]) == rows[0][2*i+1] for i in range(k))
        left = [third(rows[0][2*i], rows[0]) for i in range(k)]
        right = [third(rows[1][2*i+1], rows[1]) for i in range(k)]
        boundary = [(left[i], rows[0][2*i]) for i in range(k)] + [
            (right[i], rows[1][2*i+1]) for i in range(k)]
        boundary_set = set(boundary)
        assert len(boundary_set) == 2*k
        outside = set(graph) - deleted
        open_phi = {d: rho[d] if d[1] in deleted else rho[alpha[d]]
                    for d in alpha if d[0] in outside}
        assert set(open_phi) == set(open_phi.values())
        expected = [(i-1) % k for i in range(k)] + [k+(i+1) % k for i in range(k)]
        for j, b in enumerate(boundary):
            c = boundary[expected[j]]
            current = c
            for _ in range(3):
                current = phi[current]
            assert current == alpha[b]
            n = len(face_of[c])
            assert n in (5, 6)
            lengths[n] += 1
            current = b
            for step in range(1, n-2):
                current = open_phi[current]
                if step < n-3:
                    assert current not in boundary_set
            assert current == c
        components = list(nx.connected_components(graph.subgraph(outside)))
        assert len(components) == 2
        ls = next(s for s in components if left[0] in s)
        rs = next(s for s in components if right[0] in s)
        assert ls != rs and set(left) <= ls and set(right) <= rs
        widths[k] += 1
        cases.append(dict(width=k, end_faces=2*k, shore_sizes=sorted(map(len, components))))
    assert len(cases) == 20 and sum(lengths.values()) == 720
    return dict(evidence='Independent finite implication replay; not a Lean occurrence certificate.',
                source_map=source['id'], two_row_starts=len(cases),
                widths=dict(sorted(widths.items())), end_face_paths_checked=sum(lengths.values()),
                end_face_length_histogram=dict(sorted(lengths.items())),
                literal_row_rotation_steps_checked=rotation_steps,
                earlier_exterior_boundary_hits=0, opposite_returns_verified=True,
                two_shore_components_verified=True, cases=cases,
                global_occurrence_coverage_proved=False, full_occurrence_census_repeated=False,
                colouring_search_repeated=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE/'residual-coverage-probe.json')
    parser.add_argument('--output', type=Path, default=HERE/'two-row-short-faces.json')
    args = parser.parse_args()
    assert args.output.resolve() not in (args.input.resolve(), Path(__file__).resolve())
    result = replay(args.input)
    result['input_sha256'] = hashlib.sha256(args.input.read_bytes()).hexdigest()
    result['program_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ('two_row_starts', 'end_face_paths_checked',
                     'end_face_length_histogram', 'earlier_exterior_boundary_hits')}))


if __name__ == '__main__':
    main()
