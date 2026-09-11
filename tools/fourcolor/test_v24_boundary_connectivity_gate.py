import json
from pathlib import Path
import unittest

from v24_boundary_connectivity_gate import boundary, boundary_join, realize, run, sew


class BoundaryConnectivityTests(unittest.TestCase):
    def test_complete_gate(self):
        data = run()
        self.assertEqual([r['sides'] for r in data['rows']], [12, 29, 81, 233, 30])
        self.assertEqual(sum(r['sewings'] for r in data['rows']), 62735)
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_boundary_connectivity_gate.json'
        self.assertEqual(data, json.loads(receipt.read_text()))

    def test_component_count_alone_is_insufficient(self):
        a, b = realize((0, 0, 1, 1)), realize((0, 1, 0, 1))
        self.assertEqual(len(set(boundary(*a)[0])), len(set(boundary(*b)[0])))
        self.assertEqual(sew(a, a)[1], 2)
        self.assertEqual(sew(a, b)[1], 1)

    def test_unobserved_component_must_not_disappear(self):
        a, b = (2, (), (0,)), (1, (), (0,))
        self.assertEqual(boundary_join(boundary(*a)[0], boundary(*b)[0])[1], 1)
        self.assertEqual(sew(a, b)[1], 2)

    def test_parallel_seams_and_internal_loops(self):
        a, b = (1, ((0, 0),), (0, 0)), (1, (), (0, 0))
        self.assertEqual(sew(a, b)[1], 1)
        self.assertEqual(boundary_join(boundary(*a)[0], boundary(*b)[0])[1], 1)

    def test_different_interior_sizes_same_partition(self):
        a, b = realize((0, 0, 0, 0)), realize((0, 0, 0, 0), True)
        self.assertNotEqual(a[0], b[0])
        self.assertEqual(boundary(*a), boundary(*b))


if __name__ == '__main__':
    unittest.main()
