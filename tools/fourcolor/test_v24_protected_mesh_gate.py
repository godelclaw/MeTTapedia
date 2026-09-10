import unittest

from v24_protected_mesh_gate import check_family, closed, enclosed_mark_control, extract, run, split_grid


class ProtectedMeshTests(unittest.TestCase):
    def test_between_branch_vertex_blocks_full_paths(self):
        rows, cols, adjacency = split_grid(6, 6)
        mark = 2 * (2 * 6 + 3) + 1
        self.assertNotIn(mark, range(0, 72, 2))
        rr, cc = extract(rows, cols, {mark}, 5, 5)
        self.assertNotIn(2, rr)
        self.assertNotIn(3, cc)
        check_family(rows, adjacency)
        check_family(cols, adjacency)

    def test_buffer_uses_off_mesh_attachment(self):
        rows, cols, adjacency = split_grid(3, 3)
        # Vertex zero has degree one; a lateral attachment preserves degree <= 3.
        adjacency[18] = {0}
        adjacency[0].add(18)
        self.assertTrue(all(18 not in path for path in rows + cols))
        self.assertEqual(closed(adjacency, {18}, 1), {0, 18})
        self.assertEqual(closed(adjacency, {18}, 2), {0, 1, 18})

    def test_empty_marks_and_index_order(self):
        rows, cols, adjacency = split_grid(3, 4)
        self.assertEqual(extract(rows, cols, set(), 3, 4), ([0, 1, 2], [0, 1, 2, 3]))
        self.assertEqual(closed(adjacency, set(), 5), set())

    def test_under_sized_request_rejected(self):
        rows, cols, _ = split_grid(2, 2)
        with self.assertRaises(AssertionError):
            extract(rows, cols, {0}, 2, 2)

    def test_edge_disjointness_and_positive_path_length_checked(self):
        rows, _, adjacency = split_grid(2, 2)
        with self.assertRaises(AssertionError):
            check_family([rows[0], rows[0]], adjacency)
        with self.assertRaises(AssertionError):
            check_family([[0]], adjacency)

    def test_carrier_avoidance_does_not_clear_interior(self):
        result = enclosed_mark_control()
        self.assertTrue(result['carrier_avoids_mark'])
        self.assertTrue(result['mark_strictly_inside_cell'])
        self.assertTrue(result['cubic'])
        self.assertTrue(result['bridgeless'])
        self.assertTrue(result['tait_colourable'])
        self.assertEqual((result['vertices'], result['edges']), (22, 33))
        self.assertFalse(result['target_counterexample_class'])

    def test_three_buffer_radii(self):
        result = run()
        self.assertEqual([c['radius'] for c in result['cases']], [0, 1, 2])
        self.assertTrue(all(c['forbidden_vertices'] <= 2 * 4 ** c['radius']
                            for c in result['cases']))


if __name__ == '__main__':
    unittest.main()
