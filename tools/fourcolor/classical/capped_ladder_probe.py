#!/usr/bin/env python3
"""Replay literal ladder sewing, shared reconstruction and physical repair.

The geometry check covers twelve widths. Exhaustive normalized target
witnesses cover four small widths. These finite checks are separate from
the all-width Lean proofs and do not establish arbitrary-map occurrence.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from adjacent_source_splice_probe import cycles
from adjacent_source_target_kempe_probe import Splice

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor'
PAIRS = ((1, 2), (1, 3), (2, 3))

if not __debug__:
    raise SystemExit('Assertions are required for the replay.')


class Ladder(Splice):
    """Use the existing actual-edge checker with literal ladder rotations."""

    def __init__(self, width):
        self.width = width
        n = 2 * width
        self.vertices = list(range(n))
        self.darts = [(v, i) for v in self.vertices for i in range(3)]
        self.alpha = {d: [((d[0]-1) % n, 1), ((d[0]+1) % n, 0),
                          (n-1-d[0], 2)][d[1]] for d in self.darts}
        self.rho = {(v, i): (v, (i+1) % 3) for v, i in self.darts}
        self.phi = {d: self.rho[self.alpha[d]] for d in self.darts}
        inverse = {e: d for d, e in self.phi.items()}
        self.edge_keys = sorted({('cross', min(d, self.alpha[d])) for d in self.darts}
                                | {('polygon', d) for d in self.darts})
        self.ids = {e: i for i, e in enumerate(self.edge_keys)}
        self.stars = {d: (self.ids['cross', min(d, self.alpha[d])],
                          self.ids['polygon', d], self.ids['polygon', inverse[d]])
                      for d in self.darts}
        incidences = {i: [] for i in range(len(self.edge_keys))}
        for d, star in self.stars.items():
            assert len(set(star)) == 3
            for edge in star:
                incidences[edge].append(d)
        assert all(len(ds) == 2 and ds[0] != ds[1] for ds in incidences.values())
        self.endpoints = {edge: tuple(ds) for edge, ds in incidences.items()}
        self.root = (0, 0)
        self.root_star = self.stars[self.root]

    def geometry(self):
        n = len(self.vertices)
        assert all(self.alpha[self.alpha[d]] == d for d in self.darts)
        assert all(d[0] != self.alpha[d][0] for d in self.darts)
        faces = cycles(self.phi)
        outer = next(face for face in faces if (0, 1) in face)
        assert {d[0] for d in outer} == set(self.vertices)
        assert len(outer) == n
        assert sorted(map(len, faces)) == sorted([2, 2] + [4]*(self.width-1) + [n])
        assert all(len({min(d, self.alpha[d]) for d in face}) == len(face) for face in faces)
        assert n - len(self.darts)//2 + len(faces) == 2
        assert len(self.edge_keys) == 9*self.width
        source_ids = {min(d, self.alpha[d]) for d in self.darts}
        assert len(source_ids) == 3*self.width
        adjacent_pairs = {tuple(sorted((d[0], self.alpha[d][0]))) for d in self.darts}
        parallel = len(source_ids)-len(adjacent_pairs)
        assert parallel == 2
        return dict(width=self.width, source_vertices=n, source_edges=len(source_ids),
                    source_faces=len(faces), expanded_vertices=len(self.darts),
                    parallel_edge_surplus=parallel, spanning_face_length=len(outer))

    def field(self, source):
        values = [0] * len(self.edge_keys)
        for d, star in self.stars.items():
            a, b = source[d[0]], source[self.alpha[d][0]]
            assert a in (1, 2, 3) and b in (1, 2, 3) and a != b
            for e, value in zip(star, (a ^ b, b, a)):
                assert values[e] in (0, value)
                values[e] = value
        assert self.valid(tuple(values))
        return tuple(values)


def projection(width, vertex):
    n = 2*width
    return n-1 if vertex == 0 else 0 if vertex == n+1 else vertex-1


def sewing(small, large):
    n = len(small.vertices)
    retained = {d for d in large.darts if 0 < d[0] < n+1}
    sewn = {d: large.alpha[d] for d in retained}
    sewn[(1, 0)], sewn[(n, 1)] = (n, 1), (1, 0)
    assert set(sewn.values()) == retained
    checks = 0
    for d in small.darts:
        old = (d[0]+1, d[1])
        expected = small.alpha[d]
        assert sewn[old] == (expected[0]+1, expected[1])
        assert large.rho[old] == (small.rho[d][0]+1, small.rho[d][1])
        if large.alpha[old] in retained:
            assert sewn[old] == large.alpha[old]
        assert projection(small.width, large.alpha[old][0]) == small.alpha[d][0]
        checks += 1
    assert len(large.darts) == len(small.darts)+6
    return checks


def replay():
    geometry, repairs = [], []
    for width in range(1, 13):
        small, large = Ladder(width), Ladder(width+1)
        record = small.geometry()
        large.geometry()
        record['sewn_dart_checks'] = sewing(small, large)
        geometry.append(record)
        if width > 4:
            continue
        spanning = next(face for face in cycles(small.phi) if (0, 1) in face)
        digest = hashlib.sha256()
        counts, components = Counter(), Counter()
        for original in small.colourings():
            q = small.corners(original)
            source = {d[0]: q[d] for d in spanning}
            canonical = small.field(source)
            current = original
            swaps = 0
            for a, b in PAIRS:
                corners = small.corners(current)
                error = {d: corners[d] ^ source[d[0]] for d in small.darts}
                assert all(error[small.phi[d]] == error[d] for d in small.darts)
                selected = {e for e, (kind, d) in enumerate(small.edge_keys)
                            if kind == 'polygon' and error[d] == (a ^ b)}
                actual = [set(component) for _, pair, component in small.raw_moves(current)
                          if pair == [a, b] and selected.intersection(component)]
                assert all(component <= selected for component in actual)
                assert set().union(*actual) == selected
                assert sum(map(len, actual)) == len(selected)
                swaps += len(actual)
                current = tuple((a ^ b ^ c) if e in selected else c
                                for e, c in enumerate(current))
                assert small.valid(current)
                assert all(current[e] == original[e] for e, (kind, _) in enumerate(small.edge_keys)
                           if kind == 'cross')
                digest.update(bytes(current))
            assert current == canonical and small.coherent(current)
            counts['inputs'] += 1
            counts['changed'] += current != original
            components[swaps] += 1
            terminal = {v: small.corners(current)[v, 0] for v in small.vertices}
            restored = {v: terminal[projection(width, v)] for v in large.vertices}
            rebuilt = large.field(restored)
            assert all(restored[v+1] == terminal[v] for v in small.vertices)
            for d in small.darts:
                assert tuple(rebuilt[e] for e in large.stars[d[0]+1, d[1]]) == \
                       tuple(current[e] for e in small.stars[d])
            digest.update(bytes(rebuilt))
        repairs.append(dict(width=width, inputs=counts['inputs'], changed=counts['changed'],
                            individual_component_histogram={str(count): n
                                                            for count, n in sorted(components.items())},
                            witness_sha256=digest.hexdigest()))
    sources = ['CappedLadderRotation.lean', 'CappedLadderEndReduction.lean',
               'CappedLadderFamilyGSLT.lean', 'CappedLadderAudit.lean']
    return dict(schema=1, geometry_widths=len(geometry), sewing_checks=sum(r['sewn_dart_checks'] for r in geometry),
                arbitrary_target_inputs=sum(r['inputs'] for r in repairs),
                nontrivial_repairs=sum(r['changed'] for r in repairs),
                region_stages=3, parallel_edge_ids_retained=True,
                retained_star_observations_preserved_after_repair=True,
                all_initial_cross_observations_preserved=True,
                colouring_counts_preserved=False, catalogue_entries_removed=0,
                geometry=geometry, finite_repairs=repairs,
                source_sha256={name: hashlib.sha256((LEAN/name).read_bytes()).hexdigest()
                               for name in sources if (LEAN/name).exists()},
                checker_sha256={name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                                for name in ['capped_ladder_probe.py', 'adjacent_source_splice_probe.py',
                                             'adjacent_source_target_kempe_probe.py']})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = HERE/'capped-ladder-probe.json'
    result = replay()
    if args.check:
        assert result == json.loads(path.read_text()), 'Saved replay differs.'
    else:
        path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ['geometry_widths', 'sewing_checks',
                                                'arbitrary_target_inputs', 'nontrivial_repairs']}))


if __name__ == '__main__':
    main()
