from itertools import combinations, permutations, product
import json
from pathlib import Path
import unittest

from v24_deletion_orbit_gate import colorings, incidence
from v24_goldberg import make_goldberg_graph
from v24_vertex_transfer_gate import (
    alphabet, check_literal, closure, evaluate, extract, literal_graph, run, step, valid,
)


class VertexTransferTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = run()

    def test_receipt_and_calibration(self):
        path = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_vertex_transfer_gate.json'
        self.assertEqual(self.receipt, json.loads(path.read_text()))
        for row in self.receipt['controls']:
            expected = {'tetrahedron': 6, 'dodecahedron': 60,
                        'Petersen_nonplanar_zero_control': 0}[row['control']]
            self.assertEqual(row['count'], expected)
        self.assertEqual(self.receipt['width3_alphabet'], 96)
        self.assertEqual(self.receipt['width3_closure'],
                         dict(raw_reachable=10, subset_reachable=4, nerode_classes=4,
                              subset_sizes=[0, 1, 3, 6]))

    def test_alphabet_complete_by_independent_raw_scan(self):
        # Scan all raw star injections and all wire arrays, rather than
        # using the production generator's consumed/produced partition.
        found = set()
        for l in range(4):
            for r in range(4):
                for star in permutations(range(l + r), 3):
                    for wires in product((None,) + tuple(range(l)), repeat=r):
                        letter = l, r, star, wires
                        if valid(letter):
                            found.add(letter)
        self.assertEqual(found, set(alphabet(3)))

    def test_literal_incidence_and_count(self):
        for letter in alphabet(3):
            n, edges, boundary = literal_graph(letter)
            inc = incidence(n, edges)
            self.assertEqual(len(inc[0]), 3)
            self.assertTrue(all(len(row) == 1 for row in inc[1:]))
            self.assertEqual(len(boundary), letter[0] + letter[1])
            self.assertGreater(check_literal(letter), 0)

    def test_raw_subset_and_language_counts_independently(self):
        # Build labelled relations from literal edge colourings, not step().
        relations = []
        for letter in alphabet(3):
            l = letter[0]
            n, edges, boundary = literal_graph(letter)
            rel = set()
            for c in colorings(n, edges):
                b = tuple(c[e] for e in boundary)
                rel.add((b[:l], b[l:]))
            relations.append(rel)
        states = [frozenset({()})]
        transitions = []
        for s in states:
            row = []
            for rel in relations:
                target = frozenset(y for x, y in rel if x in s)
                if target not in states:
                    states.append(target)
                row.append(states.index(target))
            transitions.append(row)
        pairs = list(combinations(range(len(states)), 2))
        distinguishable = {p for p in pairs if (() in states[p[0]]) != (() in states[p[1]])}
        while True:
            enlarged = distinguishable | {
                (i, j) for i, j in pairs
                if any(tuple(sorted((a, b))) in distinguishable
                       for a, b in zip(transitions[i], transitions[j]))}
            if enlarged == distinguishable:
                break
            distinguishable = enlarged
        self.assertEqual(len(states), 4)
        self.assertEqual(len(set().union(*states)), 10)
        self.assertEqual(distinguishable, set(pairs))
        self.assertEqual(closure(tuple(alphabet(3)))['nerode_classes'], len(states))

    def test_persistent_wire_identity_is_observable(self):
        a = (4, 3, (0, 1, 6), (2, 3, None))
        swapped = (4, 3, (0, 1, 6), (3, 2, None))
        self.assertTrue(valid(a) and valid(swapped))
        self.assertEqual(step(a, (0, 1, 0, 1)), [(0, 1, 2)])
        self.assertEqual(step(swapped, (0, 1, 0, 1)), [(1, 0, 2)])
        self.assertNotEqual(step(a, (0, 1, 0, 1)), step(swapped, (0, 1, 0, 1)))

    def test_coordinate_reindexing(self):
        a = (4, 3, (0, 1, 6), (2, 3, None))
        pin, pout = (2, 0, 3, 1), (1, 2, 0)  # old index -> new index
        star = tuple(pin[i] if i < 4 else 4 + pout[i - 4] for i in a[2])
        wires = [None] * 3
        for j, i in enumerate(a[3]):
            wires[pout[j]] = None if i is None else pin[i]
        b = 4, 3, star, tuple(wires)
        self.assertTrue(valid(b))
        for x in product(range(3), repeat=4):
            xx = tuple(x[pin.index(i)] for i in range(4))
            expected = {tuple(y[pout.index(j)] for j in range(3)) for y in step(a, x)}
            self.assertEqual(set(step(b, xx)), expected)

    def test_reordered_complete_sweeps(self):
        edges = [tuple(e) for e in make_goldberg_graph(1)['primal_edges']]
        for es in (edges, list(reversed(edges)), [(v, u) for u, v in edges]):
            for order in (list(range(20)), list(reversed(range(20)))):
                self.assertEqual(evaluate(extract(20, es, order))[0], 60)

    def test_parallel_edges_and_disconnected_multiplicity(self):
        self.assertEqual(evaluate(extract(2, [(0, 1)] * 3, [0, 1]))[0], 6)
        tetrahedron = list(combinations(range(4), 2))
        edges = tetrahedron + [(u + 4, v + 4) for u, v in tetrahedron]
        for order in (list(range(8)), [0, 4, 1, 5, 2, 6, 3, 7]):
            self.assertEqual(evaluate(extract(8, edges, order))[0], 36)

    def test_reject_corrupt_letters_and_inputs(self):
        good = (4, 3, (0, 1, 6), (2, 3, None))
        for bad in ((-1, 3, (0, 1, 2), (None,) * 3),
                    (4, 3, (0, 0, 6), (2, 3, None)),
                    (4, 3, (0, 1, 7), (2, 3, None)),
                    (4, 3, (0, 1, 6), (2, 2, None)),
                    (4, 3, (0, 1, 6), (2, 3, 0))):
            self.assertFalse(valid(bad))
        with self.assertRaises(AssertionError):
            step(good, (0, 1, 2))
        with self.assertRaises(AssertionError):
            step(good, (0, 1, 2, 3))
        with self.assertRaises(AssertionError):
            extract(4, list(combinations(range(4), 2)), [0, 1, 1, 3])
        birth = (0, 3, (0, 1, 2), (None, None, None))
        merge = (3, 2, (0, 1, 4), (2, None))
        dead = (2, 1, (0, 1, 2), (None,))
        bad_after_dead = (1, 2, (0, 0, 2), (None, None))
        with self.assertRaises(AssertionError):
            evaluate([birth, merge, dead, bad_after_dead])
        with self.assertRaises(AssertionError):
            evaluate([birth])


if __name__ == '__main__':
    unittest.main()
