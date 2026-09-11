import unittest
import json
from pathlib import Path

from v24_small_cut_transfer_gate import run, sew_open, transfer
from v24_structural_bridge_gate import cut_profile


class SmallCutTransferTests(unittest.TestCase):
    def test_full_gate(self):
        result = run()
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_small_cut_transfer_gate.json'
        self.assertEqual(result, json.loads(receipt.read_text()))
        self.assertEqual(len(result['rows']), 20)
        for row in result['rows']:
            sizes = [12, 29, 81, 233]
            self.assertEqual(row['sewings'], sizes[row['left'] + row['seam']] *
                             sizes[row['seam'] + row['right']])

    def test_three_piece_associativity(self):
        sides = [(2, ((0, 1),), (0, 1)), (2, (), (0, 1)),
                 (3, ((0, 1), (0, 1)), (0, 1)), (1, ((0, 0),), (0, 0))]
        for a in sides:
            for b in sides:
                for c in sides:
                    pa, pb, pc = map(lambda s: cut_profile(*s), (a, b, c))
                    lhs = transfer(transfer(pa, pb, 1, 1, 1), pc, 1, 1, 1)
                    rhs = transfer(pa, transfer(pb, pc, 1, 1, 1), 1, 1, 1)
                    graph = sew_open(sew_open(a, b, 1, 1, 1), c, 1, 1, 1)
                    self.assertEqual(lhs, rhs)
                    self.assertEqual(lhs, cut_profile(*graph))

    def test_saturation_retains_the_whole_profile(self):
        a = (2, ((0, 1), (0, 1), (0, 1)), (0, 1))
        b = (2, ((0, 1),), (0, 1))
        result = transfer(cut_profile(*a), cut_profile(*b), 1, 1, 1)
        self.assertTrue(any(s[3] == 2 for s in result))
        self.assertEqual(result, cut_profile(*sew_open(a, b, 1, 1, 1)))

    def test_malformed_arity_rejected(self):
        with self.assertRaises(AssertionError):
            transfer({((False,), False, True, 0)}, {((False,), False, True, 0)}, 1, 1, 1)


if __name__ == '__main__':
    unittest.main()
