import unittest
from itertools import product

from v24_square_physical_observable_gate import (
    COLORS, equality_profile, extensions, pairings, profiles, rotation_faces, run,
)


class PhysicalObservableTests(unittest.TestCase):
    def test_pairing_completeness_and_unique_endpoints(self):
        for size, expected in ((4, 3), (6, 15), (10, 945)):
            ps = list(pairings(list(range(size))))
            self.assertEqual(len(ps), expected)
            self.assertEqual(len(set(ps)), expected)
            for p in ps:
                self.assertEqual(sorted(x for edge in p for x in edge), list(range(size)))

    def test_digon_direct_vertex_enumeration(self):
        # Independent of the pairing enumerator: assign the two digon edges,
        # inspect its two proper vertices, and require equality with the wire.
        ps = ((0, 6), (1, 4), (2, 5), (3, 7), (8, 9))
        observed = equality_profile(profiles(2, ps)[1])
        for w in product(COLORS, repeat=4):
            direct = sum(w[2] == w[3] and a == w[2]
                         and len({w[0], a, b}) == len({w[1], a, b}) == 3
                         for a, b in product(COLORS, repeat=2))
            self.assertEqual(observed[w], direct)
            self.assertEqual(direct, sum(x[0] == w[2] for x in extensions(w)))

    def test_full_and_equality_observations_are_different(self):
        result = run()
        self.assertFalse(result['full_profile_nonnegative_decomposition'])
        self.assertTrue(result['boundary_equality_exact_replacement'])
        self.assertEqual(result['census'][1]['equality_exact'], 216)

    def test_suppression_flips_equality_to_inequality(self):
        self.assertEqual(sum(x[0] == 1 for x in extensions((1, 1, 1, 1))), 0)
        self.assertEqual(sum(x[0] == 2 for x in extensions((1, 1, 2, 2))), 1)
        self.assertEqual(sum(x[0] == 2 for x in extensions((1, 2, 2, 1))), 0)

    def test_terminal_order_and_sphere(self):
        data = run()['replacement']
        faces = rotation_faces(data['capped_edges'], data['capped_rotation'])
        self.assertEqual(6 - 9 + len(faces), 2)
        self.assertIn([(5, 1), (8, 1), (7, 1), (6, 1)], faces)

    def test_rotation_rejects_wrong_vertex(self):
        data = run()['replacement']
        data['capped_rotation'][0][0] = (0, 1)
        with self.assertRaises(AssertionError):
            rotation_faces(data['capped_edges'], data['capped_rotation'])


if __name__ == '__main__':
    unittest.main()
