import json
from pathlib import Path
import unittest

from v24_absolute_topology_gate import enumerated
from v24_deletion_orbit_gate import incidence
from v24_plantri_seed_audit import graph_record, parse_ascii_graph
from v24_smoothing_cycle_gate import common_cycles, complement_cycles
from v24_smoothing_provenance_gate import (ASCII, run, smooth, lift,
    matching_targets, try_exchange)


class SmoothingProvenanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = run()

    def test_receipt(self):
        root = Path(__file__).resolve().parents[2]
        saved = json.loads((root / 'results/fourcolor/v24_smoothing_provenance_gate.json').read_text())
        saved.pop('census', None)
        self.assertEqual(json.loads(json.dumps(self.receipt)), saved)

    def test_source_not_smaller_has_normal_form(self):
        r = self.receipt
        self.assertEqual(r['geometry']['girth'], 5)
        self.assertEqual(r['geometry']['dual_vertex_connectivity_at_least'], 5)
        self.assertEqual(r['smaller_girth'], 4)
        self.assertEqual(r['graph']['primal_vertex_count'], 30)
        self.assertEqual(r['smaller']['primal_vertex_count'], 28)

    def test_actual_lift_and_outside_preservation(self):
        g = graph_record(parse_ascii_graph(ASCII), 0)
        h, images, marks, deleted = smooth(g, 0)
        c = self.receipt['exchange_witness']['coloring']
        pair, cycle = common_cycles(28, h['primal_edges'], c, marks)[0]
        result = lift(g, h, images, marks, deleted, c, (pair, cycle))
        self.assertIn(bytes(result), enumerated(30, g['primal_edges']))
        for old, new in images.items():
            if new not in cycle:
                self.assertEqual(result[old], c[new])

    def test_matching_exchange_is_not_a_two_color_swap(self):
        r = self.receipt
        c, witness = r['bad_seed'], r['exchange_witness']
        self.assertEqual({c[e] for e in witness['carrier']}, {0, 1, 2})
        self.assertEqual(set(witness['before']) ^ set(witness['after']),
                         set(witness['carrier']))
        inc = incidence(28, r['smaller']['primal_edges'])
        for row in inc:
            self.assertEqual(len(set(row) & set(witness['after'])), 1)

    def test_joining_does_not_imply_evenness(self):
        r = self.receipt
        p = r['parity_failure']
        f = complement_cycles(28, r['smaller']['primal_edges'], frozenset(p['after']))
        self.assertEqual(sum(len(c) % 2 for c in f), 2)
        self.assertTrue(any(set(r['marks']) <= set(c) for c in f))

    def test_absent_target_is_not_assumed(self):
        r = self.receipt
        self.assertIsNone(try_exchange(28, r['smaller']['primal_edges'], r['marks'],
                                      r['bad_seed'], []))


if __name__ == '__main__':
    unittest.main()
