#!/usr/bin/env python3
"""Replay physical face-phase normalization on actual source-splice outputs.

Keep one calibrated source choice throughout three region stages. Check the
original edge identities, complete mask saturation, its decomposition into
actual bichromatic components, every intermediate Tait field and exact final
reconstruction. Region stages and individual components are counted separately.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from adjacent_source_splice_probe import cycles
from adjacent_source_target_kempe_probe import Splice
from source_alternating_boundary_probe import geometry
from two_cell_source_repair_probe import Map, cube_rotation, decoded_rotation, prism

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor'
PAIRS = ((1, 2), (1, 3), (2, 3))

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
            spanning = [face for face in faces if {d[0] for d in face} == set(s.vertices)]
            if not spanning:
                continue
            assert all(len({min(d, s.alpha[d]) for d in face}) == len(face) for face in faces)
            stage_histogram, component_histogram = Counter(), Counter()
            inputs = changed = 0
            witness_digest = hashlib.sha256()
            for original in s.colourings():
                assert s.valid(original)
                q = s.corners(original)
                source = {}
                for d in spanning[0]:
                    assert d[0] not in source or source[d[0]] == q[d]
                    source[d[0]] = q[d]
                assert set(source) == set(s.vertices)
                for d in s.darts:
                    assert source[d[0]] in (1, 2, 3)
                    assert source[d[0]] != source[s.alpha[d][0]]
                    assert source[d[0]] ^ source[s.alpha[d][0]] == original[s.stars[d][0]]
                canonical = tuple(source[d[0]] ^ source[s.alpha[d][0]] if kind == 'cross'
                                  else source[s.alpha[d][0]] for kind, d in s.edge_keys)
                current = original
                nonempty_stages = total_components = 0
                witness_digest.update(bytes(original))
                for a, b in PAIRS:
                    q = s.corners(current)
                    error = {d: q[d] ^ source[d[0]] for d in s.darts}
                    assert all(error[s.phi[d]] == error[d] for d in s.darts)
                    selected = {e for e, (kind, d) in enumerate(s.edge_keys)
                                if kind == 'polygon' and error[d] == (a ^ b)}
                    assert all(current[e] in (a, b) for e in selected)
                    for star in s.stars.values():
                        active = {e for e in star if current[e] in (a, b)}
                        assert not selected.intersection(active) or active <= selected
                    components = [set(component) for _, pair, component in s.raw_moves(current)
                                  if pair == [a, b] and selected.intersection(component)]
                    assert all(component <= selected for component in components)
                    assert set().union(*components) == selected
                    assert sum(map(len, components)) == len(selected)
                    nonempty_stages += bool(selected)
                    total_components += len(components)
                    current = tuple((a ^ b ^ colour) if e in selected else colour
                                    for e, colour in enumerate(current))
                    assert s.valid(current)
                    s.corner_reconstruction(current)
                    assert all(current[e] == original[e] for e, (kind, _) in enumerate(s.edge_keys)
                               if kind == 'cross')
                    after = s.corners(current)
                    assert all(after[d] ^ source[d[0]] == (0 if error[d] == (a ^ b) else error[d])
                               for d in s.darts)
                    witness_digest.update(bytes(current))
                assert current == canonical and s.coherent(current)
                changed += current != original
                stage_histogram[nonempty_stages] += 1
                component_histogram[total_components] += 1
                inputs += 1
            records.append(dict(map=m.name, omitted=[u, v], inputs=inputs,
                                repaired_inputs=changed, source_vertices=len(s.vertices),
                                target_vertices=len(s.darts), parallel_source_edges=s.parallel_source,
                                parallel_target_edges=s.parallel_target,
                                nonempty_region_stages=dict(sorted(stage_histogram.items())),
                                individual_components=dict(sorted(component_histogram.items())),
                                all_intermediate_fields_tait=True, all_cross_edges_preserved=True,
                                exact_terminal_source_image=True, global_renaming_used=False,
                                witness_fields_sha256=witness_digest.hexdigest()))
    sources = ['DualTruncateFacePhaseKempe.lean', 'DualTruncateFacePhaseGSLT.lean',
               'AdjacentSourceFacePhaseReduction.lean', 'DualTruncateFacePhaseExample.lean',
               'DualTruncateFacePhaseAudit.lean']
    checkers = ['adjacent_source_face_phase_probe.py', 'adjacent_source_target_kempe_probe.py',
                'adjacent_source_splice_probe.py', 'source_alternating_boundary_probe.py',
                'two_cell_source_repair_probe.py', 'dual_truncate_open_patch_probe.py',
                'dual_truncate_geometry_probe.py']
    return dict(schema=1, evidence='independent exhaustive finite program replay', records=records,
                recognized_interfaces=len(records), normalized_target_inputs=sum(r['inputs'] for r in records),
                changed_inputs=sum(r['repaired_inputs'] for r in records), region_stages_per_route=3,
                maximum_individual_components=max(max(r['individual_components']) for r in records),
                kernel_repair_fixtures=1, kernel_splice_fixtures=0, catalogue_entries_removed=0,
                source_sha256={p: hashlib.sha256((LEAN/p).read_bytes()).hexdigest() for p in sources},
                checker_sha256={p: hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in checkers},
                scope='Exact physical normalization on six recognized splice interfaces, with all cross '
                      'observations fixed. Three region stages may require more than three individual '
                      'component switches. This finite replay is separate from the general Lean proof '
                      'and its nontrivial theta repair fixture; it supplies no recursive or universal coverage.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = replay()
    result = json.loads(json.dumps(result))
    destination = HERE / 'adjacent-source-face-phase-probe.json'
    if args.check:
        assert result == json.loads(destination.read_text())
    else:
        destination.write_text(json.dumps(result, indent=2) + '\n')
    print(f"{result['normalized_target_inputs']} target inputs; {result['changed_inputs']} nontrivial repairs; "
          f"{result['recognized_interfaces']} interfaces; three region stages, "
          f"at most {result['maximum_individual_components']} individual components in this census. "
          'Finite program evidence.')


if __name__ == '__main__':
    main()
