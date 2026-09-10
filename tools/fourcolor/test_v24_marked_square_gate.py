import unittest

from v24_marked_square_gate import extensions, reconstruct, reduced, run, valid_seed


class MarkedSquareGateTest(unittest.TestCase):
    def test_complete_constructor_gate(self):
        result = run()
        self.assertEqual(result['words'], 81)
        self.assertEqual(result['tagged_checks'], 972)

    def test_literal_image_does_not_preserve_zero(self):
        word = (1, 1, 1, 1)
        self.assertEqual(sum(x[0] == 1 for x in extensions(word)), 0)
        for side in (0, 1):
            for image in (0, 1):
                self.assertEqual(sum(x[image] == 1 for x in reduced(word, side)), 1)

    def test_seed_is_not_just_any_nonzero_colour(self):
        self.assertFalse(valid_seed((1, 1, 1, 1), 1))
        self.assertTrue(valid_seed((1, 1, 1, 1), 2))
        self.assertEqual(reconstruct((1, 1, 1, 1), 2), (2, 3, 2, 3))

    def test_nonzero_reconstruction_alone_misses_closure(self):
        word = (2, 1, 1, 1)
        self.assertTrue(all(reconstruct(word, 2)))
        self.assertFalse(valid_seed(word, 2))
        self.assertEqual(extensions(word), [])


if __name__ == '__main__':
    unittest.main()
