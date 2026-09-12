import random
import unittest

from v24_source_roundtrip_gate import check, run


class SourceRoundtrip(unittest.TestCase):
    def test_random_source_sweeps(self):
        result = run(100)
        self.assertEqual(result["roundtrip_failures"], 0)
        self.assertGreater(result["disconnected_prefixes"], 0)

    def test_rotation_negative_control(self):
        alpha = {0: 3, 3: 0, 1: 5, 5: 1, 2: 4, 4: 2}
        self.assertEqual(check(alpha, [1, 0], random.Random(0))[0], 0)
        self.assertGreater(check(alpha, [1, 0], random.Random(0), reverse=True)[0], 0)


if __name__ == "__main__":
    unittest.main()
