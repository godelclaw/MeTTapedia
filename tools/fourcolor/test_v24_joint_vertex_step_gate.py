"""Joint physical semantics and finite-state controls, not 4CT coverage."""

import json
from pathlib import Path
import unittest

from v24_joint_vertex_step_gate import (
    bounded_closure, check_sweep, encode_rotation, joint_step, run, structurally_accepting,
)


class JointVertexStepTests(unittest.TestCase):
    def test_receipt_reproduces(self):
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_joint_vertex_step_gate.json'
        self.assertEqual(json.loads(json.dumps(run())), json.loads(receipt.read_text()))

    def test_preregistered_controls(self):
        result = run()
        self.assertEqual(result['checked_prefixes'], 1594)
        self.assertEqual(result['tetra_genus_histogram'], {0: 48, 1: 336})
        petersen = result['controls'][-1]
        self.assertEqual((petersen['count'], petersen['genus']), (0, 2))

    def test_full_width_three_fixed_point(self):
        result = bounded_closure(3)
        self.assertEqual(result['alphabet'], 96)
        self.assertEqual(result['states'], 71)
        self.assertEqual(result['transitions'], 2658)
        self.assertEqual(result['genus_rejections'], 504)
        self.assertEqual(result['accepting_states'], 1)

    def test_hidden_closed_component_is_not_forgotten(self):
        initial = ((), frozenset({((), False, False, 0)}), frozenset({()}))
        start = (0, 3, (0, 1, 2), (None, None, None))
        finish = (3, 0, (2, 1, 0), ())
        self.assertFalse(structurally_accepting(initial))
        first = joint_step(initial, start)
        self.assertFalse(structurally_accepting(first))
        theta = joint_step(first, finish)
        self.assertTrue(structurally_accepting(theta))
        two_theta = joint_step(joint_step(theta, start), finish)
        self.assertFalse(structurally_accepting(two_theta))
        self.assertIn(((), True, True, 0), two_theta[1])
        self.assertEqual(check_sweep((start, finish, start, finish))['components'], 2)

    def test_empty_support_does_not_skip_syntax_validation(self):
        empty = ((), frozenset({((), False, False, 0)}), frozenset())
        with self.assertRaises(AssertionError):
            joint_step(empty, (0, 3, (0, 0, 2), (None, None, None)))
        with self.assertRaises(AssertionError):
            joint_step(empty, (3, 0, (0, 1, 2), ()))

    def test_rotation_not_prefiltered_as_spherical(self):
        tetra = [[1, 2, 3], [0, 3, 2], [0, 1, 3], [0, 2, 1]]
        sphere = check_sweep(encode_rotation(tetra, range(4)))
        tetra[0].reverse()
        torus = check_sweep(encode_rotation(tetra, range(4)))
        self.assertEqual(sphere['count'], torus['count'])
        self.assertEqual((sphere['genus'], torus['genus']), (0, 1))


if __name__ == '__main__':
    unittest.main()
