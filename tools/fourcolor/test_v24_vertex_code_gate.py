import unittest

from v24_vertex_code_gate import factor, partition_valid, run
from v24_joint_vertex_step_gate import check_sweep


class VertexCodeGate(unittest.TestCase):
    def test_exhaustive_partition_and_colour_correspondence(self):
        self.assertEqual(run(), dict(bound=3, raw_codes=20820,
                                     valid_codes=96, colour_pairs=18144))

    def test_persistent_coordinates_are_not_sorted_away(self):
        letter = 4, 3, (0, 1, 6), (3, 2, None)
        self.assertEqual(factor(letter), ((0, 1), (0, 1), (2,),
                                          (('in', 0), ('in', 1), ('out', 0))))

    def test_duplicate_wire_rejected(self):
        self.assertFalse(partition_valid((4, 3, (0, 1, 6), (2, 2, None))))

    def test_dropped_port_rejected(self):
        self.assertFalse(partition_valid((4, 1, (0, 1, 4), (None,))))

    def test_completed_components_accumulate_mass_at_width_three(self):
        birth = (0, 3, (0, 1, 2), (None, None, None))
        close = (3, 0, (0, 2, 1), ())
        for n in range(1, 9):
            actual = check_sweep([birth, close] * n, direct_colours=False)
            self.assertEqual(actual['components'], n)
            self.assertEqual(actual['euler'], 2 * n)
            self.assertEqual(actual['genus'], 0)
            self.assertEqual(actual['count'], 6 ** n)


if __name__ == '__main__':
    unittest.main()
