from collections import Counter
from itertools import permutations, product
import json
from pathlib import Path
import unittest

from v24_deletion_orbit_gate import colorings, incidence
from v24_plantri_seed_audit import graph_record
from v24_vertex_splice_gate import (
    closed_structure, decode, encode_rotation, profile, run, splice, supports,
    transport_profile,
)
from v24_vertex_transfer_gate import evaluate


def literal_open(letters):
    n, pairs, frontier = decode(letters)
    edges = [(a // 3, b // 3) for a, b in pairs]
    edges += [(d // 3, n + i) for i, d in enumerate(frontier)]
    return n + len(frontier), edges, len(pairs)


def literal_support(letters):
    n, edges, start = literal_open(letters)
    return frozenset(tuple(c[start:]) for c in colorings(n, edges))


def independent_faces(n, pairs, orientations=None):
    """Walk (edge, endpoint) flags, independently of the gate's phi map."""
    around = [[] for _ in range(n)]
    for e, pair in enumerate(pairs):
        for side, d in enumerate(pair):
            around[d // 3].append((d % 3, (e, side)))
    rows = [[flag for _, flag in sorted(row)] for row in around]
    if orientations is not None:
        rows = [row if direction == 1 else list(reversed(row))
                for row, direction in zip(rows, orientations)]
    unseen = {(e, side) for e in range(len(pairs)) for side in (0, 1)}
    cycles = []
    while unseen:
        start = min(unseen)
        flag, cycle = start, []
        while not cycle or flag != start:
            assert flag in unseen
            unseen.remove(flag)
            cycle.append(flag)
            e, side = flag
            opposite = (e, 1 - side)
            row = rows[pairs[e][1 - side] // 3]
            flag = row[(row.index(opposite) + 1) % len(row)]
        cycles.append(cycle)
    return cycles


class VertexSpliceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = run()

    def test_receipt_and_scope(self):
        path = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_vertex_splice_gate.json'
        self.assertEqual(json.loads(json.dumps(self.receipt)), json.loads(path.read_text()))
        self.assertEqual(self.receipt['tally'], dict(
            orders=160, support_repeats=743, level0_cases=743, level0_failures=72,
            level1_cases=671, level2_cases=671, level3_cases=564,
            repair_attempts=72, repaired=72))

    def test_actual_decoding_and_independent_faces(self):
        for witness in self.receipt['specimens'].values():
            letters, order = witness['letters'], witness['order']
            n, pairs, frontier = decode(letters, close=True)
            self.assertEqual(n, len(order))
            self.assertEqual(frontier, [])
            for d, f in pairs:
                self.assertEqual(witness['rotations'][order[d // 3]][d % 3], order[f // 3])
                self.assertEqual(witness['rotations'][order[f // 3]][f % 3], order[d // 3])
            record = graph_record(witness['rotations'], 0)
            self.assertEqual(len(independent_faces(n, pairs)), len(record['face_cycles']))
            for candidate in (letters, splice(letters, *witness['cuts']),
                              splice(letters, *witness['cuts'], witness['repair']['match'])):
                cn, cpairs, _ = decode(candidate, close=True)
                cycles = independent_faces(cn, cpairs)
                result = closed_structure(candidate)
                self.assertEqual(result['faces'], len(cycles))
                self.assertEqual(result['euler'], cn - len(cpairs) + len(cycles))
                self.assertEqual(sorted(flag for cycle in cycles for flag in cycle),
                                 [(e, s) for e in range(len(cpairs)) for s in (0, 1)])
                self.assertTrue(all(len(row) == 3 for row in incidence(
                    cn, [(d // 3, f // 3) for d, f in cpairs])))

    def test_exact_prefix_support_and_port_transport(self):
        for witness in self.receipt['specimens'].values():
            letters = witness['letters']
            i, j = witness['cuts']
            si, sj = literal_support(letters[:i]), literal_support(letters[:j])
            self.assertEqual(si, supports(letters[:i])[-1])
            self.assertEqual(sj, supports(letters[:j])[-1])
            self.assertEqual(si, sj)
            self.assertEqual(len(si), witness['support_size'])
            pi, pj = profile(*decode(letters[:i])), profile(*decode(letters[:j]))
            self.assertNotEqual(pi['face_return'], pj['face_return'])
            match = witness['repair']['match']
            self.assertEqual(frozenset(tuple(x[p] for p in match) for x in si), sj)
            moved = transport_profile(pi, match)
            self.assertEqual(moved['face_return'], pj['face_return'])
            self.assertEqual(moved['partition'], pj['partition'])
            # Transport is a genuine coordinate conjugacy, not just equal cycle counts.
            for perm in permutations(range(witness['width'])):
                inverse = tuple(perm.index(i) for i in range(len(perm)))
                restored = transport_profile(transport_profile(pi, perm), inverse)
                self.assertEqual(restored, {key: pi[key]
                                          for key in ('face_return', 'partition', 'failures')})

    def test_colouring_existence_not_total_multiplicity(self):
        for name, witness in self.receipt['specimens'].items():
            letters = witness['letters']
            candidates = [letters, splice(letters, *witness['cuts']),
                          splice(letters, *witness['cuts'], witness['repair']['match'])]
            counts = []
            for candidate in candidates:
                n, edges, _ = literal_open(candidate)
                count = len(colorings(n, edges))
                self.assertEqual(evaluate(candidate)[0], count)
                self.assertGreater(count, 0)
                counts.append(count)
            self.assertEqual(counts, [6, 6, 6] if name == '0' else [72, 24, 24])

    def test_bad_rotation_is_not_a_nonplanar_graph_claim(self):
        witness = self.receipt['specimens']['simple']
        n, pairs, _ = decode(splice(witness['letters'], *witness['cuts']), close=True)
        histogram = Counter(n - len(pairs) + len(independent_faces(n, pairs, turns))
                            for turns in product((1, -1), repeat=n))
        self.assertEqual(histogram, {0: 54, 2: 2, -2: 200})
        self.assertTrue(witness['smaller']['simple'])
        self.assertFalse(witness['smaller']['admissible'])
        self.assertTrue(witness['repair']['smaller']['simple'])
        self.assertTrue(witness['repair']['smaller']['admissible'])

    def test_parallel_candidate_is_allowed(self):
        witness = self.receipt['specimens']['0']
        candidate = splice(witness['letters'], *witness['cuts'], witness['repair']['match'])
        self.assertTrue(closed_structure(candidate)['admissible'])
        self.assertFalse(closed_structure(candidate)['simple'])
        n, pairs, _ = decode(candidate, close=True)
        self.assertEqual(n, 2)
        self.assertEqual(len(pairs), 3)
        self.assertTrue(all({d // 3, f // 3} == {0, 1} for d, f in pairs))

    def test_boundary_first_return_face_formula(self):
        # Boundary return is a candidate for a general Euler gluing proof.
        # Check its cycle formula against literal splices for every matching
        # of each saved pair, including matchings which do not preserve Count.
        def cycle_count(perm):
            self.assertEqual(sorted(perm), list(range(len(perm))))
            todo, count = set(range(len(perm))), 0
            while todo:
                point = min(todo)
                while point in todo:
                    todo.remove(point)
                    point = perm[point]
                count += 1
            return count

        for witness in self.receipt['specimens'].values():
            letters, (i, j) = witness['letters'], witness['cuts']
            n = len(letters)
            opposite = encode_rotation(witness['rotations'], list(reversed(witness['order'])))
            p = profile(*decode(letters[:i]))
            q = profile(*decode(opposite[:n-j]))
            for match in permutations(range(witness['width'])):
                rp = transport_profile(p, match)['face_return']
                rq = q['face_return']
                seam_cycles = cycle_count(tuple(rp[rq[s]] for s in range(len(rq))))
                faces = p['internal_faces'] + q['internal_faces'] + seam_cycles
                euler = (p['euler'] + q['euler'] - len(match)
                         - cycle_count(rp) - cycle_count(rq) + seam_cycles)
                literal = closed_structure(splice(letters, i, j, match))
                self.assertEqual(faces, literal['faces'])
                self.assertEqual(euler, literal['euler'])

    def test_reject_malformed_splices(self):
        witness = self.receipt['specimens']['0']
        letters, (i, j) = witness['letters'], witness['cuts']
        with self.assertRaises(AssertionError):
            splice(letters, i, j, (0, 0, 1))
        with self.assertRaises(AssertionError):
            splice(letters, j, i)
        with self.assertRaises(AssertionError):
            splice(letters, 1, 2)
        with self.assertRaises(AssertionError):
            decode(letters[:-1], close=True)
        with self.assertRaises(AssertionError):
            decode([letters[1]])
        with self.assertRaises(AssertionError):
            transport_profile(witness['before'], (1, 1, 2))
        with self.assertRaises(AssertionError):
            encode_rotation(witness['rotations'], [0, 1, 1, 3])


if __name__ == '__main__':
    unittest.main()
