from collections import Counter
from itertools import combinations, permutations, product
import json
from pathlib import Path
import unittest

from v24_positive_face_resolution_gate import (
    basis_profiles, endpoint_profile, face_profile, pairings, run,
)


def edge_enumeration(vertices, boundary, pairs):
    result = Counter()
    for colors in product(range(3), repeat=len(pairs)):
        slots = [None] * (3 * vertices + boundary)
        for (a, b), color in zip(pairs, colors):
            slots[a] = slots[b] = color
        if all(len(set(slots[3*v:3*v+3])) == 3 for v in range(vertices)):
            result[tuple(slots[3*vertices:])] += 1
    return result


class PositiveResolutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = json.loads(json.dumps(run()))

    def test_receipt(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_positive_face_resolution_gate.json"
        self.assertEqual(self.result, json.loads(path.read_text()))

    def test_complete_carrier_and_obstruction(self):
        self.assertEqual(sum(c["endpoint_pairings"] for c in self.result["classes"]), 135240)
        self.assertEqual(sum(c["nonempty"] for c in self.result["classes"]), 59460)
        self.assertTrue(self.result["positive_resolution_ruled_out"])
        for n in (5, 11):
            self.assertEqual(list(pairings(list(range(n)))), [])
        self.assertEqual((3 * 4 + 5) % 2, 1)

    def test_independent_edge_enumeration(self):
        for ps in pairings(list(range(8))):
            self.assertEqual(endpoint_profile(1, 5, ps), edge_enumeration(1, 5, ps))
        cases = (
            ((0,9),(1,10),(2,3),(4,11),(5,6),(7,12),(8,13)),
            ((0,3),(1,4),(2,6),(5,9),(7,10),(8,11),(12,13)),
            ((0,3),(1,4),(2,5),(6,9),(7,10),(8,11),(12,13)),
            ((0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13)),
        )
        for ps in cases:
            self.assertEqual(endpoint_profile(3, 5, ps), edge_enumeration(3, 5, ps))

    def test_cycle_boundary_recurrence(self):
        counts = face_profile(5)
        for word in product(range(3), repeat=5):
            number = 0
            for start in range(3):
                edge, good = start, True
                for port in word:
                    if edge == port:
                        good = False
                        break
                    edge = 3 - edge - port
                number += int(good and edge == start)
            self.assertEqual(counts[word], number)

    def test_five_witnesses_cover_every_profile(self):
        target = face_profile(5)
        words = []
        for a, b in combinations(range(5), 2):
            word = tuple(1 if i == a else 2 if i == b else 0 for i in range(5))
            if word not in target:
                words.append(word)
        self.assertEqual(len(words), 5)
        basis = basis_profiles()
        self.assertEqual(len(basis), 25)
        for support in basis:
            self.assertTrue(set(words) & set(support))

    def test_vertex_slot_relabelling(self):
        ps = ((0,9),(1,10),(2,3),(4,11),(5,6),(7,12),(8,13))
        expected = endpoint_profile(3, 5, ps)
        for v in range(3):
            for p in permutations(range(3)):
                labels = list(range(14))
                labels[3*v:3*v+3] = [3*v+i for i in p]
                changed = tuple((labels[a], labels[b]) for a,b in ps)
                self.assertEqual(endpoint_profile(3, 5, changed), expected)


if __name__ == "__main__":
    unittest.main()
