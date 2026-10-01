#!/usr/bin/env python3
"""Replay spanning-face calibration on literal adjacent-source splice outputs.

Recognize one actual face touching every retained source vertex. For every
normalized target Tait witness, its corners on that face reconstruct a
proper nonzero source witness with exactly the same cross-edge colours.
Parallel edge identities and complete joint fields are retained.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from adjacent_source_splice_probe import cycles
from adjacent_source_target_kempe_probe import Splice
from source_alternating_boundary_probe import geometry
from two_cell_source_repair_probe import Map, cube_rotation, decoded_rotation, prism

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor'

if not __debug__:
    raise SystemExit('Assertions are required for the replay.')


def replay():
    records = []
    maps = [Map('triangular-prism', decoded_rotation('DualTruncateSourceDomainExample.lean')),
            Map('cube', cube_rotation()), Map('pentagonal-prism', prism(5)),
            Map('hexagonal-prism', prism(6))]
    for m in maps:
        geometry(m)
        for u, v in sorted(m.source.edges())[:3]:
            if len((set(m.source[u])-{v}) | (set(m.source[v])-{u})) != 4:
                continue
            s = Splice(m, u, v)
            faces = cycles(s.phi)
            assert all(len({min(d, s.alpha[d]) for d in face}) == len(face) for face in faces)
            spanning = [face for face in faces if {d[0] for d in face} == set(s.vertices)]
            record = dict(map=m.name, omitted=[u, v], source_vertices=len(s.vertices),
                          target_vertices=len(s.darts), parallel_source_edges=s.parallel_source,
                          parallel_target_edges=s.parallel_target, face_lengths=list(map(len, faces)),
                          spanning_faces=len(spanning), calibrated_target_witnesses=0,
                          all_cross_edges_preserved=None)
            if spanning:
                face = spanning[0]
                for state in s.colourings():
                    assert s.valid(state)
                    q = s.corners(state)
                    source = {}
                    for d in face:
                        assert d[0] not in source or source[d[0]] == q[d]
                        source[d[0]] = q[d]
                    assert set(source) == set(s.vertices)
                    assert all(c in (1, 2, 3) for c in source.values())
                    for d in s.darts:
                        assert source[d[0]] != source[s.alpha[d][0]]
                        assert source[d[0]] ^ source[s.alpha[d][0]] == state[s.stars[d][0]]
                    expanded = tuple(source[d[0]] ^ source[s.alpha[d][0]] if kind == 'cross'
                                     else source[s.alpha[d][0]] for kind, d in s.edge_keys)
                    assert s.valid(expanded) and s.coherent(expanded)
                    s.corner_reconstruction(expanded)
                    assert all(expanded[e] == state[e] for e, (kind, _) in enumerate(s.edge_keys)
                               if kind == 'cross')
                    record['calibrated_target_witnesses'] += 1
                record['all_cross_edges_preserved'] = True
                record['spanning_face'] = [list(d) for d in face]
            records.append(record)
    sources = ['RotationClosedEdgePotential.lean', 'DualTruncateSpanningFace.lean',
               'AdjacentSourceSpanningFaceReduction.lean', 'DualTruncateSpanningFaceExample.lean',
               'DualTruncateSpanningFaceAudit.lean']
    checkers = ['adjacent_source_spanning_face_probe.py', 'adjacent_source_target_kempe_probe.py',
                'adjacent_source_splice_probe.py', 'source_alternating_boundary_probe.py',
                'two_cell_source_repair_probe.py', 'dual_truncate_open_patch_probe.py',
                'dual_truncate_geometry_probe.py']
    return dict(schema=1, evidence='independent exhaustive finite program replay', records=records,
                interfaces_tested=len(records), spanning_face_interfaces=sum(bool(r['spanning_faces']) for r in records),
                calibrated_target_witnesses=sum(r['calibrated_target_witnesses'] for r in records),
                kernel_geometry_fixtures=1, kernel_splice_fixtures=0, catalogue_entries_removed=0,
                source_sha256={p: hashlib.sha256((LEAN/p).read_bytes()).hexdigest() for p in sources},
                checker_sha256={p: hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in checkers},
                scope='Six recognized splice interfaces admit exact calibration of every normalized target witness. '
                      'The four interfaces without a spanning face are outside this mechanism. '
                      'The generic Lean theorem and the separate theta geometry fixture have their own audit. '
                      'No physical Kempe history, recursive domain closure or universal coverage follows from this replay.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = replay()
    destination = HERE / 'adjacent-source-spanning-face-probe.json'
    if args.check:
        assert result == json.loads(destination.read_text())
    else:
        destination.write_text(json.dumps(result, indent=2) + '\n')
    print(f"{result['calibrated_target_witnesses']} normalized target witnesses calibrated on "
          f"{result['spanning_face_interfaces']} of {result['interfaces_tested']} interfaces; "
          'all cross-edge colours preserved. Finite program evidence.')


if __name__ == '__main__':
    main()
