"""Controls and exact replay for the generic component-fusion gate."""

import json
from pathlib import Path
import unittest

from v24_component_fusion_gate import check, components, run


class ComponentFusionGateTests(unittest.TestCase):
    def test_components_do_not_walk_through_deleted_vertices(self):
        self.assertEqual(components({0, 2}, [(0, 1), (1, 2)]),
                         [frozenset({0}), frozenset({2})])

    def test_harmless_boundary_contact(self):
        self.assertEqual(check({0, 1, 2}, [(0, 1), (1, 2)], {0, 1}),
                         [(True, True, False)])

    def test_two_components_fuse(self):
        self.assertEqual(check({0, 1, 2}, [(0, 1), (1, 2)], {0, 2}),
                         [(False, True, True), (False, True, True)])

    def test_identity_and_empty_embeddings(self):
        self.assertEqual(check({0, 1, 2}, [(0, 1)], set()), [])
        self.assertEqual(check({0, 1, 2}, [(0, 1)], {0, 1, 2}),
                         [(True, False, False), (True, False, False)])

    def test_unrelated_large_component_does_not_fuse(self):
        self.assertEqual(check({0, 1, 2, 3}, [(0, 1), (2, 3)], {0, 2}),
                         [(True, True, False), (True, True, False)])

    def test_fixed_census_and_replay(self):
        result = run()
        self.assertEqual(sum(row['graphs'] for row in result['census']), 1099)
        self.assertEqual(sum(row['components'] for row in result['census']), 47785)
        self.assertEqual(result['minimum_balance_checks'], 9996)
        self.assertEqual(result['joint_minimum_checks'], 4190)
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_component_fusion_gate.json'
        self.assertEqual(result, json.loads(receipt.read_text()))


if __name__ == '__main__':
    unittest.main()
