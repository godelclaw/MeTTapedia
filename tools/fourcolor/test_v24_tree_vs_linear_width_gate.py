import unittest

from v24_tree_vs_linear_width_gate import (decomposition_width, is_bridgeless,
                                           is_planar, is_simple_cubic,
                                           linear_width, linear_width_at_most,
                                           prism, tube_tree, vertex_count)


class TreeVsLinearWidthGate(unittest.TestCase):
    def test_witness_lies_in_the_headline_class(self):
        for depth in (0, 1, 2, 3):
            edges, _, _ = tube_tree(depth)
            n = vertex_count(edges)
            self.assertTrue(is_simple_cubic(edges), depth)
            self.assertTrue(is_bridgeless(edges, n), depth)
            self.assertTrue(is_planar(edges), depth)

    def test_branch_width_is_constant_in_depth(self):
        widths = []
        for depth in (1, 2, 3, 4, 5):
            edges, nodes, children = tube_tree(depth)
            widths.append(decomposition_width(edges, nodes, children))
        self.assertEqual(widths, [4, 4, 4, 4, 4])

    def test_linear_width_grows(self):
        self.assertEqual(linear_width(*self._g(0))[0], 4)
        self.assertEqual(linear_width(*self._g(1))[0], 6)
        self.assertEqual(linear_width(*self._g(2))[0], 6)

    def test_linear_width_lower_bounds_are_proved_not_assumed(self):
        """exhausting the search at k proves LP > k"""
        edges, n = self._g(1)
        self.assertFalse(linear_width_at_most(edges, n, 5))
        self.assertTrue(linear_width_at_most(edges, n, 6))

    def test_a_twenty_four_vertex_witness_already_exceeds_width_four(self):
        """the closure completes at width four; this map needs six"""
        edges, nodes, children = tube_tree(1)
        n = vertex_count(edges)
        self.assertEqual(vertex_count(edges), 24)
        self.assertLessEqual(decomposition_width(edges, nodes, children), 4)
        self.assertFalse(linear_width_at_most(edges, n, 4))
        self.assertFalse(linear_width_at_most(edges, n, 5))

    def test_control_stays_flat(self):
        """a family with both widths bounded: the measurement discriminates"""
        for k in (4, 6, 8, 10):
            edges = prism(k)
            self.assertEqual(linear_width(edges, vertex_count(edges))[0], 5)

    def _g(self, depth):
        edges, _, _ = tube_tree(depth)
        return edges, vertex_count(edges)


if __name__ == "__main__":
    unittest.main()
