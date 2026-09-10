import unittest
import json
from pathlib import Path

from v24_cofacial_rigidity_gate import analyze, normal_form_loss, prism, run
from v24_goldberg import make_goldberg_graph


class CofacialRigidityGateTest(unittest.TestCase):
    def test_prism_is_nonvacuous_counterexample(self):
        result = run()['control']['analysis']
        self.assertEqual(result['colorings'], 30)
        self.assertEqual(len(result['rigid']), 5)
        self.assertTrue(all(r['still_connected'] for r in result['rigid']))

    def test_dodecahedron_calibration(self):
        result = analyze(make_goldberg_graph(1))
        self.assertEqual(result['colorings'], 60)
        self.assertEqual(result['tested_pairs'], 60)
        self.assertEqual(result['rigid'], [])

    def test_not_a_girth_five_control(self):
        self.assertEqual(min(map(len, prism()['face_cycles'])), 4)

    def test_smaller_maps_lose_normal_form(self):
        records = normal_form_loss()
        self.assertEqual([r['vertices'] for r in records], [18, 18])
        self.assertEqual([r['face_lengths'][0] for r in records], [4, 3])

    def test_control_receipt(self):
        receipt = json.loads((Path(__file__).resolve().parents[2] /
            'results/fourcolor/v24_cofacial_rigidity_gate.json').read_text())
        fresh = json.loads(json.dumps(run()))
        self.assertEqual(receipt['control'], fresh['control'])
        self.assertEqual(receipt['normal_form_loss'], fresh['normal_form_loss'])

    def test_geometry_checked(self):
        graph = prism()
        graph['face_cycles'].pop()
        with self.assertRaises((AssertionError, ValueError)):
            analyze(graph)


if __name__ == '__main__':
    unittest.main()
