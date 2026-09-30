#!/usr/bin/env python3
"""Test the current reduction-family supply disjunction on explicit rotations.

The branches are recognized diamonds, face-derived padded caps, and simple
alternating rows with a hexagonal output seam at width at least three.
Every original dart/phase orbit is inspected. Finite success is not global
coverage; a failure is not a minimal counterexample to Four Colour.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from alternating_lobe_probe import data, tait_colouring, lobe_from, lobe_shores
from alternating_cycle_probe import alternating_orbits, oriented_row, grow
from residual_coverage_probe import dual_truncate, inspect, short_cycles

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are replay checks.')


def examine(raw):
    result = inspect(raw)
    graph, alpha, rho, faces = data(raw['rotation'])
    face_of = {d: f for f in faces for d in f}
    two_rows = []
    for orbit in alternating_orbits(alpha, rho):
        vs = [d[0] for d, _ in orbit]
        if len(set(vs)) != len(vs) or graph.subgraph(vs).number_of_edges() != len(vs):
            continue
        row = oriented_row(graph, rho, orbit)
        history = grow(graph, alpha, rho, face_of, row)
        if history['width'] >= 3 and len(history['rows']) >= 2:
            two_rows.append(history)
    result['hexagonal_seam_cycle_starts'] = len(two_rows)
    result['covered_by_current_families'] = bool(
        result['flanked_darts'] or result['cap_rooted_occurrences'] or two_rows)
    result['first_hexagonal_seam_cycle'] = two_rows[0] if two_rows else None
    # Omit the older three-row-union conclusion: it has a different scope.
    result.pop('covered_by_occurrence_union')
    result['rotation'] = raw['rotation']
    return result


def run(fixtures, controls):
    saved = json.loads(controls.read_text())
    for relative, digest in saved['source_sha256'].items():
        assert hashlib.sha256((REPO/relative).read_bytes()).hexdigest() == digest
    inputs = [dict(id=m['id'], rotation=m['rotation']) for m in saved['maps']]
    for raw in json.loads(fixtures.read_text())['maps']:
        inputs.extend((raw, dual_truncate(raw)))
    results = []
    for raw in inputs:
        result = examine(raw)
        results.append(result)
        print(json.dumps({key: result[key] for key in ('id', 'vertices', 'flanked_darts',
              'cap_rooted_occurrences', 'hexagonal_seam_cycle_starts',
              'nonsimple_orbits', 'covered_by_current_families')}), flush=True)
    failures = [r for r in results if not r['covered_by_current_families']]
    diagnostics = []
    for raw in sorted(failures, key=lambda r: (r['vertices'], r['id'])):
        graph, alpha, rho, faces = data(raw['rotation'])
        cuts = short_cycles(raw)
        colour = tait_colouring(graph)
        assert colour is not None
        by_edge = {frozenset((u, v)): c for u, v, c in colour}
        assert set(by_edge) == {frozenset(e) for e in graph.edges()}
        assert all({by_edge[frozenset((v, w))] for w in graph[v]} == {0, 1, 2}
                   for v in graph)
        orbits = alternating_orbits(alpha, rho)
        lobes = [lobe_from(orbit, j) for orbit in orbits for j in range(len(orbit))]
        shortest = min(lobes, key=lambda l: (len(l), l))
        diagnostics.append(dict(map=raw['id'], vertices=len(graph),
                                short_dual_cycle_diagnostics=cuts,
                                tait_colour_edges=colour,
                                lobes_checked=len(lobes),
                                lobe_length_histogram=dict(sorted(Counter(map(len, lobes)).items())),
                                shortest_lobe=lobe_shores(graph, alpha, rho, faces, shortest),
                                minimal_counterexample_status_inferred=False))
    sources = [Path(__file__), fixtures, controls,
               HERE/'residual_coverage_probe.py', HERE/'alternating_cycle_probe.py',
               HERE/'alternating_lobe_probe.py', HERE/'padded_cap_recognition_probe.py',
               HERE/'padded_cap_geometry_probe.py', HERE/'padded_cap_probe.py']
    return dict(evidence='Independent finite occurrence and obstruction replay; not Lean certificates.',
                candidate='The current diamond, face-derived padded-cap and hexagonal-seam simple-cycle families cover every map in the intended all-five/six normal-form class.',
                candidate_holds_in_checked_sources=not failures,
                scope='Eight saved controls and eighteen explicit isolated-pentagon rotations of orders 60-80, each also dual-and-truncated; all rooted face traces and dart/phase orbits.',
                maps_checked=len(results),
                covered_maps=len(results)-len(failures),
                uncovered_maps=len(failures),
                vertex_count_histogram=dict(sorted(Counter(r['vertices'] for r in results).items())),
                failed_map_ids=[r['id'] for r in failures],
                maps=results, failure_diagnostics=diagnostics,
                global_coverage_proved=False, kernel_occurrence_certificate=False,
                minimality_dependent_coverage_refuted=False,
                generator_completeness_kernel_certified=False,
                source_sha256={str(p.relative_to(REPO)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sources})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures', type=Path, default=HERE/'family-supply-fixtures.json')
    parser.add_argument('--controls', type=Path, default=HERE/'residual-coverage-probe.json')
    parser.add_argument('--output', type=Path, default=HERE/'family-supply-probe.json')
    args = parser.parse_args()
    assert args.output.resolve() not in {p.resolve() for p in
                                       (args.fixtures, args.controls, Path(__file__))}
    result = run(args.fixtures, args.controls)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ('maps_checked', 'covered_maps',
                     'uncovered_maps', 'failed_map_ids')}))


if __name__ == '__main__':
    main()
