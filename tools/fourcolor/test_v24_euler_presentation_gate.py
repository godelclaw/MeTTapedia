import unittest

from v24_euler_presentation_gate import literal_defect, run, theta


class EulerPresentationGateTests(unittest.TestCase):
    def test_opposite_and_equal_rotations(self):
        self.assertEqual(literal_defect(2, theta()), (0, 4))
        self.assertEqual(literal_defect(2, theta(twisted=True)), (4, 0))

    def test_disjoint_planar_components(self):
        edges = theta() + theta(6) + theta(12)
        self.assertEqual(literal_defect(6, edges), (0, 12))

    def test_hidden_handle_cancellation(self):
        edges = theta() + theta(6, twisted=True) + theta(12, twisted=True)
        self.assertEqual(literal_defect(6, edges), (8, 4))

    def test_attachment_bridge(self):
        result = run(100)
        self.assertEqual(result["bridge_failures"], 0)
        self.assertGreater(result["attachment_steps"], 100)
        self.assertGreater(result["handle_creating_steps"], 0)


if __name__ == "__main__":
    unittest.main()
