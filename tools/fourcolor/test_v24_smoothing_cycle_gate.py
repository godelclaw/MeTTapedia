import json
from pathlib import Path
import unittest

from v24_smoothing_cycle_gate import (ASCII, MARKS, common_cycles, inverse_insertion,
    perfect_matchings, complement_cycles, run)
from v24_absolute_topology_gate import enumerated
from v24_plantri_seed_audit import graph_record, parse_ascii_graph


class SmoothingCycleTests(unittest.TestCase):
    def test_receipt(self):
        root = Path(__file__).resolve().parents[2]
        self.assertEqual(json.loads(json.dumps(run())),
                         json.loads((root / 'results/fourcolor/v24_smoothing_cycle_gate.json').read_text()))

    def test_adjacent_edges_are_positive(self):
        g = graph_record(parse_ascii_graph(ASCII), 0)
        for c in enumerated(18, g['primal_edges']):
            self.assertTrue(common_cycles(18, g['primal_edges'], c, (0, 1)))
            self.assertFalse(common_cycles(18, g['primal_edges'], c, MARKS))

    def test_nonmatching_rejected(self):
        g = graph_record(parse_ascii_graph(ASCII), 0)
        with self.assertRaises(AssertionError):
            complement_cycles(18, g['primal_edges'], frozenset())
        self.assertEqual(len(perfect_matchings(18, g['primal_edges'])), 23)

    def test_insertion_requires_disjoint_edges(self):
        r = parse_ascii_graph(ASCII)
        with self.assertRaises(AssertionError):
            inverse_insertion(r, graph_record(r, 0), (0, 1))


if __name__ == '__main__':
    unittest.main()
