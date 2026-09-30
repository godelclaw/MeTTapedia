#!/usr/bin/env python3
"""Check actual successor stars and identity seam labels in the saved residual.

This is independent finite program evidence, not a Lean occurrence
certificate. No colouring search or complete occurrence census is repeated.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

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
    widths, cases = Counter(), []
    star_darts, labels = 0, 0
    for orbit in alternating_orbits(alpha, rho):
        row = oriented_row(graph, rho, orbit)
        if row is None:
            continue
        history = grow(graph, alpha, rho, face_of, row)
        if len(history['rows']) != 2:
            continue
        old, successor = history['rows']
        k = history['width']
        assert k >= 3 and len(set(old) | set(successor)) == 4*k
        third = lambda v, r: next(u for u in graph[v] if u not in r)
        outputs = [(old[2*i+1], third(old[2*i+1], old)) for i in range(k)]
        assert all(len(face_of[d]) == 6 for d in outputs)
        for i, output in enumerate(outputs):
            x = alpha[output]
            y = alpha[rho[x]]
            assert (x[0], y[0]) == (successor[2*i], successor[2*i+1])
            expected = (
                (x, (successor[2*i], successor[2*i+1]),
                 (successor[2*i], successor[(2*i-1) % (2*k)])),
                (y, (successor[2*i+1], successor[(2*i+2) % (2*k)]),
                 (successor[2*i+1], third(successor[2*i+1], successor))))
            for base, star in zip((x, y), expected):
                d = base
                for wanted in star:
                    assert d == wanted
                    star_darts += 1
                    d = rho[d]
                assert d == base
            # The actual successor input is the same old output edge,
            # at the same index, with its dart reversed.
            successor_input = (successor[2*i], third(successor[2*i], successor))
            assert successor_input == x and alpha[successor_input] == output
            labels += 1
        assert any(len(face_of[(successor[2*i+1], third(successor[2*i+1], successor))]) == 5
                   for i in range(k))
        widths[k] += 1
        cases.append(dict(width=k, removed_vertices=4*k,
                          original_vertices=len(graph), smaller_vertices=len(graph)-4*k))
    assert len(cases) == 20 and labels == 360 and star_darts == 2160
    return dict(evidence='Independent finite successor/alignment replay; not a Lean occurrence certificate.',
                source_map=source['id'], two_row_starts=len(cases),
                widths=dict(sorted(widths.items())), collar_star_darts_checked=star_darts,
                identity_seam_labels_checked=labels,
                auxiliary_vertices_introduced=0, cases=cases,
                kernel_occurrence_certificate=False, global_occurrence_coverage_proved=False,
                full_occurrence_census_repeated=False, colouring_search_repeated=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE/'residual-coverage-probe.json')
    parser.add_argument('--output', type=Path, default=HERE/'two-row-growth.json')
    args = parser.parse_args()
    assert args.output.resolve() not in (args.input.resolve(), Path(__file__).resolve())
    result = replay(args.input)
    result['input_sha256'] = hashlib.sha256(args.input.read_bytes()).hexdigest()
    result['program_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ('two_row_starts',
                     'collar_star_darts_checked', 'identity_seam_labels_checked')}))


if __name__ == '__main__':
    main()
