from itertools import combinations, permutations
import json
from pathlib import Path
import unittest

from v24_boundary_rewire_gate import cycles, first_return, run


class BoundaryRewireTests(unittest.TestCase):
    def test_exhaustive_receipt(self):
        receipt = run()
        path = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_boundary_rewire_gate.json'
        self.assertEqual(receipt, json.loads(path.read_text()))
        self.assertEqual(sum(r['cases'] for r in receipt['rows']), 40789)
        self.assertEqual(sum(r['changed_cycle_count'] for r in receipt['rows']), 26068)

    def test_first_return_via_deleting_unmarked_cycle_entries(self):
        # Independent construction: form oriented whole cycles once, then
        # erase unmarked entries, instead of following a new walk per port.
        for n in range(6):
            for p in permutations(range(n)):
                unseen, oriented = set(range(n)), []
                while unseen:
                    a = min(unseen)
                    row = [a]
                    b = p[a]
                    while b != a:
                        row.append(b)
                        b = p[b]
                    unseen.difference_update(row)
                    oriented.append(row)
                self.assertEqual(cycles(p), {frozenset(row) for row in oriented})
                for k in range(n + 1):
                    for marks in combinations(range(n), k):
                        result = [None] * k
                        for row in oriented:
                            kept = [x for x in row if x in marks]
                            for i, a in enumerate(kept):
                                result[marks.index(a)] = marks.index(kept[(i + 1) % len(kept)])
                        self.assertEqual(tuple(result), first_return(p, marks))

    def test_untouched_cycle_and_empty_boundary(self):
        p, q, marks = (1, 0, 3, 2), (0, 1, 3, 2), (0, 1)
        self.assertEqual(cycles(p), {frozenset((0, 1)), frozenset((2, 3))})
        self.assertEqual(cycles(q), {frozenset((0,)), frozenset((1,)), frozenset((2, 3))})
        self.assertEqual(first_return(p, marks), (1, 0))
        self.assertEqual(first_return(q, marks), (0, 1))
        self.assertEqual(first_return(p, ()), ())
        self.assertEqual(first_return((), ()), ())
        self.assertEqual(cycles(()), set())

    def test_order_not_just_number_of_boundary_cycles(self):
        p, q, s = (1, 2, 0), (2, 0, 1), (1, 2, 0)
        self.assertEqual(len(cycles(p)), len(cycles(q)))
        self.assertEqual(len(cycles(tuple(p[s[i]] for i in range(3)))), 1)
        self.assertEqual(len(cycles(tuple(q[s[i]] for i in range(3)))), 3)

    def test_replacement_correction_ignores_exterior(self):
        # Different interior carriers may have different numbers of faces.
        # Equal boundary returns preserve the sewing correction, not the
        # absolute face count. Test actual permutation sewing to each exterior.
        def sewn(p, q, k, matching):
            n = len(p)
            unsewn = tuple(p) + tuple(n + x for x in q)
            partner = list(range(len(unsewn)))
            for i in range(k):
                j = n + matching[i]
                partner[i], partner[j] = j, i
            return tuple(unsewn[partner[d]] for d in range(len(unsewn)))

        cases = 0
        for k in range(4):
            representatives = {}
            for m in range(k, 5):
                for q in permutations(range(m)):
                    signature = first_return(q, tuple(range(k)))
                    old = representatives.setdefault(signature, q)
                    for n in range(k, 4):
                        for p in permutations(range(n)):
                            for matching in permutations(range(k)):
                                self.assertEqual(
                                    len(cycles(sewn(p, q, k, matching))) - len(cycles(q)),
                                    len(cycles(sewn(p, old, k, matching))) - len(cycles(old)))
                                cases += 1
        self.assertEqual(cases, 2229)

    def test_malformed_input_rejected(self):
        for p in ((0, 0), (1,), (-1, 0)):
            with self.assertRaises(AssertionError):
                cycles(p)
            with self.assertRaises(AssertionError):
                first_return(p, ())
        for marks in ((0, 0), (2,), (-1,)):
            with self.assertRaises(AssertionError):
                first_return((1, 0), marks)


if __name__ == '__main__':
    unittest.main()
