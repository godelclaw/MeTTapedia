"""Controls for absent names, aliases, padding, and invisible face arcs."""

import unittest

from v24_named_face_record_gate import named_partition, record


class NamedFaceRecordTests(unittest.TestCase):
    def test_no_names_and_empty_carrier(self):
        self.assertEqual(record((), ()), (((), ()), ()))
        self.assertEqual(record((0,), ()), (((), ()), ()))

    def test_absence_is_not_a_named_fixed_point(self):
        absent, _ = record((0,), (None,))
        present, _ = record((0,), (0,))
        self.assertEqual(absent[0], present[0])
        self.assertNotEqual(absent, present)

    def test_aliases_preserved(self):
        left, _ = record((0, 1), (0, 1, 0))
        right, _ = record((0, 1), (0, 1, 1))
        self.assertEqual(left[0], right[0])
        self.assertNotEqual(left, right)
        self.assertNotEqual(named_partition((0, 1), (0, 1, 0)),
                            named_partition((0, 1), (0, 1, 1)))

    def test_different_carriers_same_named_record(self):
        self.assertEqual(record((1, 0), (0, None, 1))[0],
                         record((2, 0, 1, 3), (0, None, 1))[0])

    def test_return_order_not_only_cycle_partition(self):
        names = (0, 1, 2, 3)
        p, q = (1, 2, 3, 0), (2, 3, 1, 0)
        self.assertEqual(named_partition(p, names), named_partition(q, names))
        self.assertNotEqual(record(p, names)[0], record(q, names)[0])


if __name__ == '__main__':
    unittest.main()
