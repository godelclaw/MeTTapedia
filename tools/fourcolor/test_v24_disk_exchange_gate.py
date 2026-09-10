"""Regression tests for the complete-boundary disk exchange control."""

import copy
import json
from pathlib import Path
import unittest

from v24_component_copy_gate import proper
from v24_disk_exchange_gate import disk_data, run
from v24_goldberg import make_goldberg_graph


class DiskExchangeGate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = json.loads(json.dumps(run()))

    def test_receipt(self):
        path = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_disk_exchange_gate.json'
        self.assertEqual(json.loads(path.read_text()), self.result)

    def test_complete_and_frozen_counts(self):
        self.assertEqual(self.result['complete_counts'], dict(full=60, left=108, right=108))
        self.assertEqual(self.result['frozen_counts'], dict(full=0, left=2, right=1))
        self.assertEqual(self.result['pair_count'], 2)
        self.assertEqual(self.result['frozen_minimum'], 6)
        self.assertEqual(len(self.result['all_minimizers']), 2)

    def test_complete_disk_boundary(self):
        disk = self.result['disk']
        self.assertEqual(len(disk['faces']), 10)
        self.assertEqual(len(disk['rim_cycle']), 8)
        self.assertEqual(len(disk['rim_edges']), 8)
        self.assertEqual(len(disk['frozen_edges']), 9)
        for pair in self.result['all_minimizers']:
            self.assertTrue(set(pair['disagreement_edges']) <= set(disk['interior_edges']))

    def test_unfrozen_escape(self):
        c = self.result['full_coloring_with_smallest_exterior_change']
        self.assertTrue(proper(20, self.result['graph']['edges'], c))
        self.assertEqual(self.result['exterior_change_edges'], [11])
        self.assertEqual(self.result['unrestricted_minimum'], 0)
        self.assertEqual([r['full_extensions'] for r in self.result['larger_disks']], [2, 2])

    def test_full_sphere_not_a_disk_with_exterior(self):
        with self.assertRaises(AssertionError):
            disk_data(make_goldberg_graph(1), set(range(12)))

    def test_missing_face_incidence_rejected(self):
        graph = copy.deepcopy(make_goldberg_graph(1))
        graph['face_cycles'][6] = graph['face_cycles'][6][:-1]
        with self.assertRaises((AssertionError, KeyError)):
            disk_data(graph, set(range(12)) - {6, 8})


if __name__ == '__main__':
    unittest.main()
