#!/usr/bin/env python3
"""Replay target Kempe choices on literal parallel-edge splice outputs.

Enumerate actual edge witnesses, preserving distinct parallel edges, and
compare physical Kempe classes with the exact coherent source image.
These finite program checks do not prove a general reachability theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, deque
from itertools import permutations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor'
from adjacent_source_splice_probe import cycles
from source_alternating_boundary_probe import boundary_order, geometry
from two_cell_source_repair_probe import Map, cube_rotation, decoded_rotation, prism

if not __debug__:
    raise SystemExit('Assertions are required for the replay.')


class Splice:
    def __init__(self, m, u, v):
        darts, self.pins = boundary_order(m, u, v)
        self.omitted = [u, v]
        self.source_before, self.target_before = len(m.source), len(m.target)
        self.vertices = sorted(set(m.source) - {u, v})
        self.darts = sorted(d for d in m.alpha if d[0] in self.vertices)
        self.alpha = {d: m.alpha[d] for d in self.darts}
        for i, j in [(0, 3), (1, 2)]:
            self.alpha[darts[i]], self.alpha[darts[j]] = darts[j], darts[i]
        self.rho = {d: m.rho[d] for d in self.darts}
        self.phi = {d: self.rho[self.alpha[d]] for d in self.darts}
        inverse = {e: d for d, e in self.phi.items()}
        assert set(self.alpha.values()) == set(self.darts)
        assert all(self.alpha[self.alpha[d]] == d for d in self.darts)
        assert all(d[0] != self.alpha[d][0] for d in self.darts)
        assert all(sum(d[0] == w for d in self.darts) == 3 for w in self.vertices)
        assert len(self.vertices) == self.source_before - 2
        assert len(self.darts) == self.target_before - 6
        reachable = {self.vertices[0]}
        while True:
            more = {self.alpha[d][0] for d in self.darts if d[0] in reachable}
            if more <= reachable:
                break
            reachable |= more
        assert reachable == set(self.vertices)
        assert len(self.vertices)-len(self.darts)//2+len(cycles(self.phi)) == 2
        self.edge_keys = sorted({('cross', min(d, self.alpha[d])) for d in self.darts}
                                | {('polygon', d) for d in self.darts})
        self.ids = {e: i for i, e in enumerate(self.edge_keys)}
        self.stars = {d: (self.ids['cross', min(d, self.alpha[d])],
                          self.ids['polygon', d], self.ids['polygon', inverse[d]])
                      for d in self.darts}
        incidences = {i: [] for i in range(len(self.edge_keys))}
        for d, star in self.stars.items():
            assert len(set(star)) == 3
            for i in star:
                incidences[i].append(d)
        assert all(len(ds) == 2 and ds[0] != ds[1] for ds in incidences.values())
        self.endpoints = {e: tuple(ds) for e, ds in incidences.items()}
        reachable = {self.darts[0]}
        while True:
            more = {d for ends in self.endpoints.values() if any(z in reachable for z in ends) for d in ends}
            if more <= reachable:
                break
            reachable |= more
        assert reachable == set(self.darts)
        target_darts = [(d, i) for d in self.darts for i in range(3)]
        def flip(x):
            d, i = x
            if i == 0:
                return self.alpha[d], 0
            if i == 1:
                return self.phi[d], 2
            return inverse[d], 1
        target_phi = {x: (flip(x)[0], (flip(x)[1]+1) % 3) for x in target_darts}
        assert len(self.darts)-len(self.edge_keys)+len(cycles(target_phi)) == 2
        self.root = self.darts[0]
        self.root_star = self.stars[self.root]
        self.parallel_target = len(self.endpoints)-len({tuple(sorted(ds)) for ds in self.endpoints.values()})
        source_edges = {frozenset((d, self.alpha[d])) for d in self.darts}
        self.parallel_source = len(source_edges)-len({tuple(sorted((d[0], self.alpha[d][0])))
                                                      for d in self.darts})

    def valid(self, state):
        return all({state[e] for e in star} == {1, 2, 3} for star in self.stars.values())

    def corners(self, state):
        return {d: state[star[2]] for d, star in self.stars.items()}

    def corner_reconstruction(self, state):
        q = self.corners(state)
        rebuilt = [0] * len(state)
        for d, star in self.stars.items():
            assert q[d] in (1, 2, 3) and q[d] != q[self.phi[d]]
            assert q[d] ^ q[self.phi[d]] == q[self.alpha[d]] ^ q[self.phi[self.alpha[d]]]
            for e, c in zip(star, (q[d] ^ q[self.phi[d]], q[self.phi[d]], q[d])):
                assert rebuilt[e] in (0, c)
                rebuilt[e] = c
        assert tuple(rebuilt) == state

    def coherent(self, state):
        q = self.corners(state)
        return all(q[d] == q[self.rho[d]] for d in self.darts)

    def defect_vertices(self, state):
        q = self.corners(state)
        return sorted({d[0] for d in self.darts if q[d] != q[self.rho[d]]})

    def normalize(self, state):
        renaming = {state[e]: i+1 for i, e in enumerate(self.root_star)}
        assert len(renaming) == 3
        return tuple(renaming[c] for c in state)

    def colourings(self):
        values = [0] * len(self.edge_keys)
        for e, c in zip(self.root_star, (1, 2, 3)):
            values[e] = c
        choices = list(permutations((1, 2, 3)))

        def visit(left):
            if not left:
                state = tuple(values)
                assert self.valid(state)
                yield state
                return
            d = max(left, key=lambda z: (sum(values[e] != 0 for e in self.stars[z]), z))
            star = self.stars[d]
            new = [e for e in star if not values[e]]
            for colours in choices:
                if any(values[e] and values[e] != c for e, c in zip(star, colours)):
                    continue
                for e, c in zip(star, colours):
                    values[e] = c
                yield from visit(left - {d})
                for e in new:
                    values[e] = 0

        yield from visit(set(self.darts) - {self.root})

    def raw_moves(self, state):
        for a, b in [(1, 2), (1, 3), (2, 3)]:
            unused = {e for e, c in enumerate(state) if c in (a, b)}
            while unused:
                e = min(unused)
                component, todo = set(), [e]
                while todo:
                    edge = todo.pop()
                    if edge in component:
                        continue
                    component.add(edge)
                    for d in self.endpoints[edge]:
                        todo.extend(f for f in self.stars[d] if f in unused and f not in component)
                unused -= component
                switched = tuple((a ^ b ^ c) if e in component else c for e, c in enumerate(state))
                assert self.valid(switched)
                yield switched, [a, b], sorted(component)

    def moves(self, state):
        for target, pair, component in self.raw_moves(state):
            yield self.normalize(target), pair, component

    def source_images(self):
        images = set()
        for values in product((1, 2, 3), repeat=len(self.vertices)):
            c = dict(zip(self.vertices, values))
            if any(c[d[0]] == c[self.alpha[d][0]] for d in self.darts):
                continue
            state = [0] * len(self.edge_keys)
            for d, star in self.stars.items():
                a, b = c[d[0]], c[self.alpha[d][0]]
                for e, value in zip(star, (a ^ b, b, a)):
                    assert state[e] in (0, value)
                    state[e] = value
            assert self.valid(state)
            images.add(self.normalize(state))
        return images

    def replay(self):
        states_list = list(self.colourings())
        states = set(states_list)
        assert len(states) == len(states_list)
        for state in states:
            self.corner_reconstruction(state)
        images = self.source_images()
        coherent = {s for s in states if self.coherent(s)}
        assert coherent == images
        unseen = set(states)
        classes = []
        while unseen:
            root = min(unseen)
            seen, todo = {root}, deque([root])
            while todo:
                state = todo.popleft()
                for target, _, _ in self.moves(state):
                    assert target in states
                    if target not in seen:
                        seen.add(target)
                        todo.append(target)
            unseen -= seen
            classes.append(dict(size=len(seen), coherent=len(seen & coherent),
                                representative=list(root),
                                corners=[self.corners(root)[d] for d in self.darts]))
        distances, parents = {s: 0 for s in coherent}, {}
        todo = deque(sorted(coherent))
        while todo:
            state = todo.popleft()
            for target, pair, component in self.moves(state):
                if target not in distances:
                    distances[target] = distances[state] + 1
                    parents[target] = (state, pair, component)
                    todo.append(target)
        stuck = []
        for state in sorted(states - coherent):
            n = len(self.defect_vertices(state))
            targets = list(self.moves(state))
            assert targets
            best = min(len(self.defect_vertices(t)) for t, _, _ in targets)
            if best >= n:
                stuck.append(dict(state=list(state), corners=[self.corners(state)[d] for d in self.darts],
                                  defect_vertices=self.defect_vertices(state), smallest_next_defects=best))
        def repair_path(state):
            path, physical = [], state
            while distances[state]:
                target, pair, component = parents[state]
                pair, component = next((p, c) for t, p, c in self.moves(state) if t == target)
                # Lift the quotient path without applying a colour renaming.
                actual_pair = [physical[self.root_star[p-1]] for p in pair]
                after = tuple((actual_pair[0] ^ actual_pair[1] ^ c) if e in component else c
                              for e, c in enumerate(physical))
                assert any(t == after and set(p) == set(actual_pair) and cs == component
                           for t, p, cs in self.raw_moves(physical))
                assert self.normalize(after) == target
                path.append(dict(state=list(physical), pair=actual_pair, component=component,
                                 after=list(after), defects_before=len(self.defect_vertices(physical)),
                                 defects_after=len(self.defect_vertices(after))))
                physical = after
                state = target
            assert state in coherent
            assert self.coherent(physical)
            return path
        longest_path = repair_path(max(distances, key=lambda s: (distances[s], s))) if parents else []
        failure_path = repair_path(tuple(stuck[0]['state'])) if stuck and tuple(stuck[0]['state']) in distances else []
        return dict(omitted=self.omitted, pins=self.pins, source_vertices=len(self.vertices),
                    source_before=self.source_before, target_before=self.target_before,
                    target_vertices=len(self.darts), target_edges=len(self.edge_keys),
                    parallel_source_edges=self.parallel_source, parallel_target_edges=self.parallel_target,
                    source_and_target_spherical=True, normalized_tait_witnesses=len(states),
                    normalized_source_images=len(coherent), kempe_classes=classes,
                    classes_without_source_image=sum(k['coherent'] == 0 for k in classes),
                    maximum_repair_steps=max(distances.values(), default=0),
                    repair_distance_histogram={str(k): v for k, v in sorted(Counter(distances.values()).items())},
                    simple_defect_descent_failures=len(stuck), defect_descent_failure_samples=stuck[:1],
                    longest_repair_path=longest_path,
                    defect_descent_failure_repair=failure_path,
                    darts=[list(d) for d in self.darts],
                    edge_keys=[[kind, list(d)] for kind, d in self.edge_keys],
                    stars=[list(self.stars[d]) for d in self.darts])


def replay():
    records = []
    for m in [Map('triangular-prism', decoded_rotation('DualTruncateSourceDomainExample.lean')),
              Map('cube', cube_rotation()), Map('pentagonal-prism', prism(5)),
              Map('hexagonal-prism', prism(6))]:
        geometry(m)
        for u, v in sorted(m.source.edges())[:3]:
            if len((set(m.source[u])-{v}) | (set(m.source[v])-{u})) != 4:
                continue
            s = Splice(m, u, v)
            record = s.replay()
            record['map'] = m.name
            records.append(record)
    lean_sources = ['AdjacentSourceSplice.lean', 'DualTruncateCornerSemantics.lean',
                    'DualTruncateCornerCoherence.lean', 'DualTruncateSourceDomainExample.lean']
    checkers = ['adjacent_source_target_kempe_probe.py', 'adjacent_source_splice_probe.py',
                'source_alternating_boundary_probe.py', 'two_cell_source_repair_probe.py',
                'dual_truncate_open_patch_probe.py', 'dual_truncate_geometry_probe.py']
    return dict(schema=1, evidence='independent program diagnostic', records=records,
                interfaces=len(records), normalized_tait_witnesses=sum(r['normalized_tait_witnesses'] for r in records),
                normalized_source_images=sum(r['normalized_source_images'] for r in records),
                kempe_classes_without_source_image=sum(r['classes_without_source_image'] for r in records),
                simple_defect_descent_failures=sum(r['simple_defect_descent_failures'] for r in records),
                kernel_finite_geometric_fixtures=0, catalogue_entries_removed=0,
                source_sha256={name: hashlib.sha256((LEAN/name).read_bytes()).hexdigest() for name in lean_sources},
                checker_sha256={name: hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in checkers},
                scope='Exhaustive normalized literal target witnesses on these ten interfaces only. '
                      'Every physical Kempe class contains a coherent source image here. The strict '
                      'incoherent-vertex-count descent fails on two hexagonal-prism side splices; '
                      'checked physical repair paths are retained. Neither a general reachability '
                      'theorem nor recursive domain closure or coverage is asserted.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = replay()
    destination = HERE/'adjacent-source-target-kempe-probe.json'
    if args.check:
        assert result == json.loads(destination.read_text())
    else:
        destination.write_text(json.dumps(result, indent=2)+'\n')
    print(f"{result['normalized_tait_witnesses']} normalized target witnesses on {result['interfaces']} interfaces; "
          f"{result['normalized_source_images']} coherent images; "
          f"{result['kempe_classes_without_source_image']} Kempe classes without an image; "
          f"{result['simple_defect_descent_failures']} strict defect-descent failures. Finite program evidence.")


if __name__ == '__main__':
    main()
