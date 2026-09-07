"""Independent negative controls for the marked-face return diagnostic."""

import itertools
import unittest

from v24_marked_face_return_gate import check, compose, compressed, extend, partition, stretch


class MarkedFaceReturnTests(unittest.TestCase):
    def test_all_rewirings_through_four_points(self):
        for n in range(1, 5):
            for p in itertools.permutations(range(n)):
                for mask in range(1 << n):
                    hit = tuple(i for i in range(n) if mask & (1 << i))
                    for tau in itertools.permutations(range(len(hit))):
                        check(p, hit, tau)

    def test_nonseam_observations_and_invisible_cycles(self):
        p = (1, 2, 0, 4, 3, 5)
        self.assertEqual(compressed(p, (0, 2, 3)), (1, 0, 2))
        check(p, (0, 2, 3), (1, 0, 2))

    def test_arc_stretch_does_not_change_record(self):
        for p in itertools.permutations(range(4)):
            for count in (0, 1, 3, 19):
                self.assertEqual(compressed(stretch(p, count), tuple(range(4))), p)

    def test_partition_is_insufficient(self):
        p, q, tau = (1, 2, 3, 0), (2, 3, 1, 0), (1, 0, 2, 3)
        self.assertEqual(partition(p), partition(q))
        self.assertNotEqual(partition(compose(p, tau)), partition(compose(q, tau)))

    def test_wrong_multiplication_order_detected(self):
        p, hit, tau = (1, 2, 3, 0), (0, 1, 2), (1, 0, 2)
        actual = compressed(compose(p, extend(tau, hit, 4)), hit)
        self.assertNotEqual(actual, compose(tau, compressed(p, hit)))


if __name__ == '__main__':
    unittest.main()
