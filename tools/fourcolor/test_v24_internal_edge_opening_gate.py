"""Regressions for the literal internal-edge opening diagnostic."""

from itertools import permutations
import json
from pathlib import Path
import unittest

from v24_internal_edge_opening_gate import run, prism, open_edges, connected
from v24_deletion_orbit_gate import colorings, incidence


class OpeningGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = run()

    def test_calibration_and_projection(self):
        for record, counts in zip(self.result['records'], [(6, 30), (30, 102)]):
            self.assertEqual((record['closed_colorings'], record['free_open_colorings']), counts)
            self.assertEqual(record['reclosed_colorings'], counts[0])
            self.assertEqual(record['single_open_colorings'], counts[0])
            self.assertNotEqual(record['escape_word'][0], record['escape_word'][2])
            self.assertTrue(record['cofacial'])

    def test_actual_endpoint_surgery(self):
        edges, _ = prism(3)
        opened, retained = open_edges(6, edges, (0, 3))
        self.assertEqual(opened[:7], [edges[i] for i in retained])
        self.assertTrue(connected(6, [edges[i] for i in retained]))
        self.assertEqual(list(map(len, incidence(10, opened))), [3]*6 + [1]*4)

    def test_all_colour_names(self):
        for record in self.result['records']:
            states = set(colorings(record['vertices']+4, record['open_edges']))
            escape = record['free_escape']
            for perm in permutations(range(3)):
                image = bytes(perm[c] for c in escape)
                self.assertIn(image, states)
                self.assertNotEqual(image[-4], image[-2])

    def test_receipt(self):
        path = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_internal_edge_opening_gate.json'
        self.assertEqual(json.loads(path.read_text()), json.loads(json.dumps(self.result)))


if __name__ == '__main__':
    unittest.main()
