import json
from pathlib import Path
import unittest

from v24_topology_viability_gate import edge_gate, hidden_by_cut, run, visibility_gate


class TopologyViabilityTests(unittest.TestCase):
    def test_receipt_reproduces(self):
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_topology_viability_gate.json'
        self.assertEqual(json.loads(json.dumps(run())), json.loads(receipt.read_text()))

    def test_exact_edge_defect(self):
        receipt = edge_gate()
        self.assertGreater(receipt["checked"], 30000)
        self.assertEqual(set(receipt["increments"]), {0, 2})
        self.assertNotEqual(receipt["wrong_face_coordinates_refuted"]["actual"],
                            receipt["wrong_face_coordinates_refuted"]["wrong"])

    def test_hidden_component_semantics(self):
        receipt = visibility_gate()
        self.assertGreater(receipt["hidden"], 0)
        self.assertGreater(receipt["nonempty_exterior_checks"], 0)

    def test_closed_and_initial_cases(self):
        self.assertIsNone(hidden_by_cut(0, (), ()))
        self.assertIsNotNone(hidden_by_cut(2, ((0, 1),), ()))
        self.assertIsNone(hidden_by_cut(2, ((0, 1),), (0,)))

    def test_hidden_isolated_vertex(self):
        self.assertIsNotNone(hidden_by_cut(3, ((0, 1),), (0, 1)))


if __name__ == "__main__":
    unittest.main()
