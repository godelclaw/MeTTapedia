import unittest

from v24_agreement_hull_gate import boundary, check, hull, prism, proper_cubic


class AgreementHullGate(unittest.TestCase):
    def test_cube_and_long_prism(self):
        for n in (4, 6, 20, 40):
            with self.subTest(n=n):
                self.assertEqual(check(n)["agreeing_hull_vertices"], 2 * n)

    def test_every_cube_seed(self):
        vertices, edges, c, d = prism(4)
        agreeing = {e for e in edges if c[e] == d[e]}
        for bits in range(256):
            seeds = {v for v in vertices if bits >> v & 1}
            closed = hull(vertices, agreeing, seeds)
            self.assertEqual(closed, vertices if seeds else set())
            self.assertFalse(boundary(agreeing, closed))
            self.assertEqual(hull(vertices, agreeing, closed), closed)

    def test_disconnected_agreement_positive_control(self):
        vertices = set(range(4))
        edges = {(0, 1), (2, 3)}
        self.assertEqual(hull(vertices, edges, {0}), {0, 1})
        self.assertFalse(boundary(edges, {0, 1}))

    def test_actual_boundary_not_disagreement_only(self):
        _, edges, c, d = prism(20)
        side = set(range(10))
        self.assertEqual(len(boundary({e for e in edges if c[e] != d[e]}, side)), 2)
        self.assertEqual(len(boundary(edges, side)), 12)

    def test_bad_colouring_rejected(self):
        vertices, edges, c, _ = prism(4)
        c[(0, 4)] = c[(0, 1)]
        self.assertFalse(proper_cubic(vertices, edges, c))

    def test_bad_circumference_rejected(self):
        for n in (0, 2, 3, 5):
            with self.assertRaises(ValueError):
                prism(n)


if __name__ == "__main__":
    unittest.main()
