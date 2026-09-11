import copy
import json
import unittest
from pathlib import Path

from v24_canonical_bond_gate import brute, run, verify_maximum
from v24_goldberg import make_goldberg_graph
from v24_unsplit_cap_sweep_gate import graph as ring_graph


class CanonicalBondTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[2]
        cls.saved = json.loads((root/'results/fourcolor/v24_canonical_bond_gate.json').read_text())

    def test_full_gate_replay(self):
        self.assertEqual(json.loads(json.dumps(run())), self.saved)
        self.assertEqual(self.saved['finite']['terminal_pairs'], 2574)
        self.assertEqual(self.saved['finite']['all_optimal_sides'], 3656)

    def test_exported_maxima(self):
        for n, row in zip((3, 5, 8, 12), self.saved['rings']):
            verify_maximum(ring_graph(n), row)
        for k, row in enumerate(self.saved['spheres'], 1):
            verify_maximum(make_goldberg_graph(k), row)
        self.assertEqual([max(r['widths']) for r in self.saved['spheres']], [6, 11, 16, 21])

    def test_missing_packing_path_rejected(self):
        row = copy.deepcopy(self.saved['spheres'][-1])
        row['maximum_witness']['paths'].pop()
        with self.assertRaises(AssertionError):
            verify_maximum(make_goldberg_graph(4), row)

    def test_incomplete_boundary_rejected(self):
        row = copy.deepcopy(self.saved['rings'][-1])
        row['maximum_witness']['cut_order'].pop()
        with self.assertRaises(AssertionError):
            verify_maximum(ring_graph(12), row)

    def test_connectedness_hypotheses_are_necessary(self):
        best, _ = brute(5, [(i, i+1) for i in range(4)], {0, 4}, {2})
        self.assertEqual(best, (2, 2, 17))
        best, _ = brute(4, [(0, 1), (2, 3)], {0}, {1})
        self.assertEqual(best, (1, 1, 1))


if __name__ == '__main__':
    unittest.main()
