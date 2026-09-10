import unittest
from itertools import permutations, product
import json
from pathlib import Path

from v24_component_copy_gate import copied, disagreement_components, proper, run


class ComponentCopyTests(unittest.TestCase):
    def test_cubic_binary_mixing_is_rigid(self):
        # Normalize the three incident nonzero colours to 0,1,2.
        # Neither a transposition nor a three-cycle admits a proper mixed star.
        distinct_valid_outputs = 0
        for old in permutations(range(3)):
            for donor in permutations(range(3)):
                valid = set()
                for choices in product(range(2), repeat=3):
                    mixed = tuple((old, donor)[choices[i]][i] for i in range(3))
                    if len(set(mixed)) == 3:
                        valid.add(mixed)
                self.assertEqual(valid, {old, donor})
                distinct_valid_outputs += len(valid)
        self.assertEqual(distinct_valid_outputs, 66)

    def test_independent_components(self):
        self.assertEqual(disagreement_components(4, [(0, 1), (2, 3)], [0, 0], [1, 1]),
                         [[0], [1]])

    def test_star_exposes_boundary_condition(self):
        # The common two-edge path misses the star's third edge.
        star = [(0, 1), (0, 2), (0, 3)]
        old, donor = bytes([0, 1, 2]), bytes([1, 2])
        self.assertTrue(proper(4, star, old))
        self.assertTrue(proper(4, star[:2], donor))
        self.assertFalse(proper(4, star, copied(old, donor, [0, 1], [0, 1])))

    def test_complete_dodecahedral_gate(self):
        result = run()
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_component_copy/summary.json'
        self.assertEqual(json.loads(json.dumps(result)), json.loads(receipt.read_text()))
        self.assertEqual(result['colorings'], [108, 108])
        self.assertEqual(result['totals']['coloring_pairs'], 11664)
        self.assertEqual(result['totals']['valid_decreasing_copies'], 528)
        witness = result['omitted_boundary_counterexample']
        self.assertTrue(proper(20, witness['edges'], witness['old']))
        self.assertTrue(proper(20, witness['common'], witness['donor']))
        self.assertFalse(proper(20, witness['edges'], witness['copied']))


if __name__ == '__main__':
    unittest.main()
