import json
from pathlib import Path
import unittest

from v24_open_euler_mass_gate import run, side_data
from v24_boundary_rewire_gate import cycles
from v24_vertex_splice_gate import prism


class OpenEulerMassTests(unittest.TestCase):
    def test_all_small_sides_and_large_controls(self):
        result = run()
        self.assertEqual(sum(row['sides'] for row in result['rows']), 5656)
        self.assertTrue(all(row['disconnected_sides'] > 0 for row in result['rows'][1:]))
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_open_euler_mass_gate.json'
        self.assertEqual(result, json.loads(receipt.read_text()))

    def test_disconnected_side_needs_component_count(self):
        d = side_data(prism(4), (0, 2))
        self.assertEqual((d['components'], d['mass'], d['ports']), (2, 8, 6))

    def test_full_closed_side_needs_properness(self):
        d = side_data(prism(3), range(6))
        self.assertEqual((d['components'], d['mass'], d['ports']), (1, 4, 0))

    def test_genus_is_not_ignored(self):
        alpha = (3, 4, 5, 0, 1, 2)
        for rho, expected in (((1, 2, 0, 5, 3, 4), 4), ((1, 2, 0, 4, 5, 3), 0)):
            faces = len(cycles(tuple(rho[alpha[d]] for d in range(6))))
            self.assertEqual(2 * 2 - 6 + 2 * faces, expected)


if __name__ == '__main__':
    unittest.main()
