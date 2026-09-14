import random
import unittest

from v24_interface_behaviour_gate import (behaviour, exhaustive_pieces,
                                          is_bridgeless, is_planar, measure,
                                          sample_map, slack_pieces,
                                          support_is_empty, validate)


class InterfaceBehaviourGate(unittest.TestCase):
    def test_sampled_maps_are_in_the_headline_class(self):
        rng = random.Random(7)
        seen = 0
        for target in (6, 8, 10, 12):
            edges = sample_map(target, rng)
            if edges is None:
                continue
            seen += 1
            verts = {v for e in edges for v in e}
            self.assertTrue(is_bridgeless(edges, verts))
            self.assertIn(is_planar(edges), (True, None))
        self.assertGreater(seen, 0)

    def test_slack_search_reproduces_exhaustive(self):
        """the counts must not be an artefact of the search order"""
        for width, row in validate().items():
            self.assertGreater(row["maps"], 0, width)
            self.assertEqual(row["missed"], 0, width)

    def test_narrow_interfaces_saturate_immediately(self):
        """width two and three settle on a fixed behaviour count"""
        for width, expected in ((2, 2), (3, 6)):
            out = measure(width, sizes=(6, 8, 10, 12), samples=3)
            self.assertEqual(out["behaviours"], expected, width)
            self.assertEqual([r["new"] for r in out["rows"][1:]], [0, 0, 0], width)

    def test_no_realized_piece_has_empty_colour_support(self):
        """the emptiness audit, on the realized image"""
        for width in (2, 3, 4):
            out = measure(width, sizes=(6, 8, 10), samples=3)
            self.assertEqual(out["empty_support"], 0, width)

    def test_behaviour_is_invariant_under_middle_relabelling(self):
        """canonicalization really quotients by the interface labelling"""
        rng = random.Random(11)
        edges = sample_map(8, rng)
        self.assertIsNotNone(edges)
        relabel = {v: (v * 5 + 3) for v in {x for e in edges for x in e}}
        other = [(relabel[u], relabel[v]) for u, v in edges]
        a = sorted({behaviour(edges, s) for s in exhaustive_pieces(edges, 3)})
        b = sorted({behaviour(other, s) for s in exhaustive_pieces(other, 3)})
        self.assertEqual(a, b)

    def test_width_five_stays_far_below_the_linear_letter_count(self):
        """the refuted linear presentation needed 3,696 letters at width five"""
        out = measure(5, sizes=(6, 8, 10, 12), samples=3)
        self.assertGreater(out["behaviours"], 50)
        self.assertLess(out["behaviours"], 1000)

    def test_support_emptiness_predicate(self):
        rng = random.Random(3)
        edges = sample_map(6, rng)
        self.assertIsNotNone(edges)
        for shore in slack_pieces(edges, 3):
            self.assertFalse(support_is_empty(behaviour(edges, shore)))


if __name__ == "__main__":
    unittest.main()
