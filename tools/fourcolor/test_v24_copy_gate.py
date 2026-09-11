"""Colour-copy constructor controls, using explicit colourings only."""

from itertools import permutations
import json
from pathlib import Path
import unittest

from v24_copy_gate import cycle, run, switch_component, validate


class CopyGateTests(unittest.TestCase):
    def test_calibrated_controls(self):
        self.assertEqual(len(run()['cycles']), 5)

    def test_every_root_and_colour_pair(self):
        for n in (2, 4, 6, 8):
            v, es, ps, ci, cb = cycle(n)
            for perm in permutations((1, 2, 3)):
                rename = dict(zip((1, 2, 3), perm))
                x, w = [rename[c] for c in ci], [rename[c] for c in cb]
                for root in range(n):
                    for other in (rename[2], rename[3]):
                        result = switch_component(v, es, ps, x, w, root, (rename[1], other))
                        self.assertEqual(len(result['endpoints']), 2)
                        self.assertIn(root, result['endpoints'])
                        self.assertEqual(len(set(result['boundary'])), 1 if n == 2 else 2)

    def test_auxiliary_ports_may_move(self):
        v, es, ps, ci, cb = cycle(8)
        result = switch_component(v, es, ps, ci, cb, 0, (1, 2))
        # Designated ports 0,2,4 split even though the other endpoint is auxiliary.
        self.assertEqual([result['boundary'][i] for i in (0, 2, 4)], [2, 1, 1])

    def test_switch_involutive(self):
        v, es, ps, ci, cb = cycle(6)
        first = switch_component(v, es, ps, ci, cb, 3, (1, 3))
        second = switch_component(v, es, ps, first['internal'], first['boundary'], 3, (1, 3))
        self.assertEqual((second['internal'], second['boundary']), (ci, cb))

    def test_non_cubic_copy_vertex_rejected(self):
        with self.assertRaisesRegex(AssertionError, 'proper cubic'):
            validate(1, [], [0, 0, 0, 0], [], [1, 1, 1, 1])

    def test_receipt_replay(self):
        path = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_copy_gate.json'
        self.assertEqual(run(), json.loads(path.read_text()))


if __name__ == '__main__':
    unittest.main()
