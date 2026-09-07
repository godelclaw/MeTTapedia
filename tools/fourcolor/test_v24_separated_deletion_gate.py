"""Small structural controls for the two-deletion coverage gate."""

import unittest

from v24_separated_deletion_gate import close, coverage, long_row, neighbors


class SeparatedDeletionTests(unittest.TestCase):
    def test_disjoint_pairs_need_not_cover_edges(self):
        edges = [(0, 1), (1, 2), (2, 3)]
        self.assertEqual(coverage(edges, (0, 1), (2, 3)), (False, False))

    def test_edge_coverage_is_not_properness_coverage(self):
        edges = [(i, i + 1) for i in range(4)]
        self.assertEqual(coverage(edges, (0, 1), (3, 4)), (True, False))

    def test_separated_pairs_cover_incident_edges(self):
        edges = [(i, i + 1) for i in range(5)]
        adj = neighbors(6, edges)
        self.assertTrue(close(adj, (0, 1)).isdisjoint(close(adj, (4, 5))))
        self.assertEqual(coverage(edges, (0, 1), (4, 5)), (True, True))

    def test_ambient_shortcut_changes_the_answer(self):
        edges = [(i, i + 1) for i in range(5)] + [(1, 4)]
        adj = neighbors(6, edges)
        self.assertFalse(close(adj, (0, 1)).isdisjoint(close(adj, (4, 5))))
        self.assertFalse(coverage(edges, (0, 1), (4, 5))[0])

    def test_cubic_row_has_local_boundary_germs(self):
        receipt = long_row(0)
        self.assertEqual(receipt["sources"], 65)
        self.assertEqual(receipt["local_boundary_germs"], 65)
        self.assertLessEqual(receipt["max_forbidden"], 32)


if __name__ == "__main__":
    unittest.main()
