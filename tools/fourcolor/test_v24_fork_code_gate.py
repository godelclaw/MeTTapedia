"""A finite code for the physical fork fold: lab controls, not 4CT coverage."""

import json
from pathlib import Path
import unittest

from v24_fork_code_gate import (
    LEAF, abstract_fork, bridged, closure, code, descriptor, direct, k4, run, theta, twist,
)


class ForkCodeTests(unittest.TestCase):
    def test_receipt_reproduces(self):
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_fork_code_gate.json'
        self.assertEqual(json.loads(json.dumps(run(), sort_keys=True)),
                         json.loads(receipt.read_text()))

    def test_leaf_code(self):
        m = k4()
        for e in range(len(m.edges)):
            self.assertEqual(code(direct(m, [e])), LEAF)

    def test_tetrahedron_fork_is_exact_in_both_rotations(self):
        for m in (k4(), twist(k4(), [0])):
            left, right = [0, 1, 2], [3, 4, 5]
            got, _ = abstract_fork(code(direct(m, left)), code(direct(m, right)),
                                   descriptor(m, left, right),
                                   components_merged=1)
            self.assertEqual(got, code(direct(m, list(range(6)))))

    def test_theta_multigraph(self):
        for m in (theta(), theta(True)):
            got, _ = abstract_fork(code(direct(m, [0])), code(direct(m, [1, 2])),
                                   descriptor(m, [0], [1, 2]))
            self.assertEqual(got, code(direct(m, [0, 1, 2])))

    def test_bridge_is_seen_at_the_root(self):
        m = bridged(k4(), k4())
        root = code(direct(m, list(range(len(m.edges)))))
        self.assertFalse(root[1])
        self.assertTrue(any(r[1] and r[2] for r in root[4]))

    def test_small_closures(self):
        self.assertEqual(closure(2)['states'], 19)
        c3 = closure(3)
        self.assertEqual((c3['states'], c3['roots'], c3['bad_roots']), (97, 2, 0))


if __name__ == '__main__':
    unittest.main()
