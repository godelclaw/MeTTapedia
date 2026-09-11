"""Regression controls for the branching-generation obstruction."""

import json
from pathlib import Path
import unittest

from v24_branching_interface_gate import cut_size, run, shapes, split_grid, supports


class BranchingInterfaceGateTests(unittest.TestCase):
    def test_exhaustive_gate(self):
        result = run()
        self.assertEqual(result["tree_threshold_checks"], 7106)
        self.assertEqual(result["overlapping_atom_checks"], 120)
        self.assertEqual(result["split_grid"]["intermediate_cuts_checked"], 30192)
        self.assertEqual(result["split_grid"]["minimum_intermediate_cut"], 2)

    def test_shape_generator(self):
        self.assertEqual([len(shapes(n)) for n in range(1, 6)], [1, 1, 2, 5, 14])

    def test_receipt_replay(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_branching_interface_gate.json"
        self.assertEqual(run(), json.loads(path.read_text()))

    def test_tiny_grid_incidence(self):
        size, edges = split_grid(1)
        self.assertEqual(size, 8)
        self.assertEqual(len(edges), 8)
        self.assertEqual(len(set(edges)), len(edges))
        self.assertTrue(all(u != v for u, v in edges))

    def test_boundary_complement_and_closed_root(self):
        size, edges = split_grid(1)
        full = (1 << size) - 1
        self.assertEqual(cut_size(edges, full), 0)
        for mask in range(1 << size):
            self.assertEqual(cut_size(edges, mask), cut_size(edges, full ^ mask))

    def test_atom_bound_is_essential(self):
        size, edges = split_grid(2)
        full = (1 << size) - 1
        root, nodes = supports(None, [full])
        self.assertEqual(root, full)
        self.assertTrue(all(cut_size(edges, s) == 0 for s in nodes))
        self.assertFalse(any(3 < s.bit_count() <= 6 for s in nodes))

    def test_growing_interfaces_are_not_excluded(self):
        size, edges = split_grid(2)

        def tree(n):
            if n == 1:
                return None
            return tree(n // 2), tree(n - n // 2)

        root, nodes = supports(tree(size), [1 << i for i in range(size)])
        self.assertEqual(root.bit_count(), size)
        self.assertTrue(all(cut_size(edges, s) <= len(edges) for s in nodes))
        self.assertTrue(any(cut_size(edges, s) > 1 for s in nodes))


if __name__ == "__main__":
    unittest.main()
