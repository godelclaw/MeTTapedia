from itertools import combinations, permutations, product
import json
from pathlib import Path
import unittest

from v24_pentagon_context_tensor_gate import (
    BAD, COEFFICIENTS, PAIRS, RELATIONS, WORDS, adversary, basis_row,
    closed_matching, delta_epsilon, epsilon, gauge, legal, noncrossing, run,
)
from v24_positive_face_resolution_gate import face_profile, pairings


class PentagonContextTensorTests(unittest.TestCase):
    def test_receipt(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_pentagon_context_tensor_gate.json"
        self.assertEqual(run(), json.loads(path.read_text()))

    def test_epsilon_and_cyclic_gauge(self):
        self.assertEqual(epsilon((0, 1, 2)), 1)
        self.assertEqual(epsilon((1, 0, 2)), -1)
        self.assertEqual(epsilon((1, 1, 2)), 0)
        for w in product(range(3), repeat=5):
            if legal(w):
                signs = [delta_epsilon(w, tuple(sorted((i, (i + 1) % 5))))
                         for i in range(5) if w[i] == w[(i + 1) % 5]]
                self.assertTrue(signs)
                self.assertEqual(set(signs), {gauge(w)})

    def test_colour_orbits_and_full_words(self):
        seen = set()
        target = face_profile(5)
        for w in WORDS:
            for p in permutations(range(3)):
                wp = tuple(p[c] for c in w)
                self.assertEqual(basis_row(wp), basis_row(w))
                seen.add(wp)
        self.assertEqual(len(seen), 60)
        for w in product(range(3), repeat=5):
            self.assertEqual(legal(w), w in seen)
            self.assertEqual(adversary(w), int(w in seen and not target[w]))
            if w not in seen:
                self.assertEqual(basis_row(w), (0,) * 10)

    def test_relations_without_symbolic_algebra(self):
        rows = [basis_row(w) for w in WORDS]
        self.assertEqual(tuple(adversary(w) for w in WORDS), BAD)
        for relation in RELATIONS:
            for i in range(len(PAIRS)):
                self.assertEqual(sum(a * row[i] for a, row in zip(relation, rows)), 0)
        for c in (COEFFICIENTS, tuple(range(-5, 5)), (1,) * 10):
            values = [sum(a * b for a, b in zip(c, row)) for row in rows]
            for relation in RELATIONS:
                self.assertEqual(sum(a * b for a, b in zip(relation, values)), 0)

    def test_boundary_order_is_not_forgotten(self):
        pentagon = face_profile(5)
        for w in product(range(3), repeat=5):
            # This is a different boundary permutation, not a plane-exterior witness.
            self.assertEqual(adversary(w), pentagon[tuple(w[2 * i % 5] for i in range(5))])
        self.assertNotEqual(tuple(adversary(w) for w in WORDS),
                            tuple(pentagon[w] for w in WORDS))

    def test_abstract_noncrossing_closure(self):
        self.assertFalse(noncrossing(((0, 2), (1, 3))))
        self.assertTrue(noncrossing(((0, 3), (1, 2))))
        support = {w for w in product(range(3), repeat=5) if adversary(w)}
        for w in support:
            for colors in combinations(range(3), 2):
                active = [i for i, c in enumerate(w) if c in colors]
                witnesses = [m for m in pairings(active) if closed_matching(w, colors, support, m)]
                self.assertTrue(witnesses)
                for m in witnesses:
                    # Independently enumerate the closure by sequential component switches.
                    reachable = {w}
                    for pair in m:
                        flipped = set()
                        for v in reachable:
                            new = list(v)
                            for i in pair:
                                new[i] = colors[1] if v[i] == colors[0] else colors[0]
                            flipped.add(tuple(new))
                        reachable |= flipped
                    self.assertLessEqual(reachable, support)


if __name__ == "__main__":
    unittest.main()
