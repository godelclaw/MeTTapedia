#!/usr/bin/env python3
"""Replay literal prism recognition and physical reconstruction independently.

Original graph darts use oriented vertex pairs. The comparison ladder uses
vertex-slot darts, so the check retains actual edge identities across two
representations. Finite replay is separate from the all-width Lean proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from adjacent_source_splice_probe import cycles
from adjacent_source_target_kempe_probe import Splice
from capped_ladder_probe import Ladder, PAIRS
from source_alternating_boundary_probe import geometry
from two_cell_source_repair_probe import Map, choices, components, source_switch

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor'

if not __debug__:
    raise SystemExit('Assertions are required for the replay.')


def prism_rows(n):
    total = 2*n
    rows = []
    for v in range(total):
        prev = n-1 if v == 0 else total-1 if v == n else v-1
        next_v = 0 if v == n-1 else n if v == total-1 else v+1
        rows.append([prev, next_v, total-1-v])
    return rows


def physical_reconstruction(original_map, small, spanning):
    totals, histogram = Counter(), Counter()
    digest = hashlib.sha256()
    for original in small.colourings():
        q = small.corners(original)
        source = {d[0]: q[d] for d in spanning}
        assert set(source) == set(small.vertices)
        canonical = Ladder.field(small, source)
        current, swaps = original, 0
        for a, b in PAIRS:
            q = small.corners(current)
            error = {d: q[d] ^ source[d[0]] for d in small.darts}
            assert all(error[small.phi[d]] == error[d] for d in small.darts)
            selected = {e for e, (kind, d) in enumerate(small.edge_keys)
                        if kind == 'polygon' and error[d] == (a ^ b)}
            actual = [set(component) for _, pair, component in small.raw_moves(current)
                      if pair == [a, b] and selected.intersection(component)]
            assert all(component <= selected for component in actual)
            assert set().union(*actual) == selected
            assert sum(map(len, actual)) == len(selected)
            swaps += len(actual)
            current = tuple((a ^ b ^ value) if e in selected else value
                            for e, value in enumerate(current))
            assert small.valid(current)
            assert all(current[e] == original[e] for e, (kind, _) in enumerate(small.edge_keys)
                       if kind == 'cross')
            digest.update(bytes(current))
        assert current == canonical and small.coherent(current)
        terminal = {v: small.corners(current)[next(d for d in small.darts if d[0] == v)]
                    for v in small.vertices}
        outside = terminal | {v: 0 for v in small.omitted}
        available = choices(outside, small.pins)
        if not available:
            repairs = []
            for pair in PAIRS:
                for component in components(original_map, outside, set(small.omitted), pair):
                    after = source_switch(outside, pair, component)
                    if choices(after, small.pins):
                        repairs.append((after, choices(after, small.pins)))
            assert repairs, 'No actual exterior component repairs the joint insertion.'
            outside, available = repairs[0]
            totals['source_component_repairs'] += 1
        restored = outside | dict(zip(small.omitted, available[0]))
        assert all(restored[a] != restored[b] for a, b in original_map.source.edges())
        rebuilt = original_map.source_field(restored)
        assert all({rebuilt[tuple(sorted((d, e)))] for e in original_map.target[d]} == {1, 2, 3}
                   for d in original_map.target)
        totals['inputs'] += 1
        totals['changed'] += current != original
        histogram[swaps] += 1
        digest.update(bytes(restored[v] for v in sorted(restored)))
    return dict(inputs=totals['inputs'], physical_repairs=totals['changed'],
                source_component_repairs=totals['source_component_repairs'],
                individual_component_histogram={str(k): v for k, v in sorted(histogram.items())},
                witness_sha256=digest.hexdigest())


def replay():
    records, repairs = [], []
    for n in range(3, 25):
        rows = prism_rows(n)
        raw = ';'.join(','.join(map(str, row)) for row in rows)
        original = Map(f'prism-{n}', raw)
        source_geometry = geometry(original)
        assert sorted(map(len, cycles(original.phi))) == sorted([n, n] + [4]*n)
        small = Splice(original, 0, 2*n-1)
        ladder = Ladder(n-1)
        transport = {(v, i): (v+1, rows[v+1][i]) for v, i in ladder.darts}
        assert set(transport.values()) == set(small.darts)
        assert len(transport) == len(set(transport.values()))
        for d in ladder.darts:
            assert transport[ladder.alpha[d]] == small.alpha[transport[d]]
            assert transport[ladder.rho[d]] == small.rho[transport[d]]
            assert transport[ladder.phi[d]] == small.phi[transport[d]]
        spanning = next(face for face in cycles(small.phi) if transport[0, 1] in face)
        assert {d[0] for d in spanning} == set(small.vertices)
        assert small.parallel_source == 2
        assert all(len({min(d, small.alpha[d]) for d in face}) == len(face)
                   for face in cycles(small.phi))
        assert small.target_before - len(small.darts) == 6
        records.append(dict(rim_width=n, source_vertices=source_geometry['vertices'],
                            source_faces=source_geometry['faces'],
                            retained_dart_checks=len(transport), smaller_vertices=len(small.vertices),
                            smaller_faces=len(cycles(small.phi)), parallel_source_surplus=2,
                            spanning_face_length=len(spanning), target_vertices_removed=6))
        if n <= 5:
            repairs.append(dict(rim_width=n, **physical_reconstruction(original, small, spanning)))
    source_names = ['PrismRungCoordinates.lean', 'PrismRungSplice.lean',
                    'PrismRungGeometry.lean', 'PrismRungReduction.lean',
                    'PrismRungAudit.lean', 'RotationSystemExactTransport.lean']
    checker_names = ['prism_rung_probe.py', 'capped_ladder_probe.py',
                     'adjacent_source_target_kempe_probe.py', 'adjacent_source_splice_probe.py',
                     'source_alternating_boundary_probe.py', 'two_cell_source_repair_probe.py',
                     'dual_truncate_open_patch_probe.py', 'dual_truncate_geometry_probe.py']
    return dict(schema=1, evidence='independent finite actual-dart and physical replay',
                geometry_widths=len(records), retained_dart_checks=sum(r['retained_dart_checks'] for r in records),
                normalized_target_inputs=sum(r['inputs'] for r in repairs),
                physical_repairs=sum(r['physical_repairs'] for r in repairs),
                source_component_repairs=sum(r['source_component_repairs'] for r in repairs),
                geometry=records, finite_repairs=repairs,
                source_sha256={name: hashlib.sha256((LEAN/name).read_bytes()).hexdigest()
                               for name in source_names},
                checker_sha256={name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                                for name in checker_names})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    destination = HERE / 'prism-rung-probe.json'
    result = replay()
    if args.check:
        assert result == json.loads(destination.read_text()), 'Saved replay differs.'
    else:
        destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in
                     ['geometry_widths', 'retained_dart_checks', 'normalized_target_inputs',
                      'physical_repairs', 'source_component_repairs']}))


if __name__ == '__main__':
    main()
