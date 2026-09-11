import json
from pathlib import Path
import unittest

from v24_bounded_cubic_trace_gate import encode
from v24_bounded_rotation_code_gate import cycle_count, face_count, gate, raw_code_count, rotation


class RotationCodeTests(unittest.TestCase):
    def test_calibrated_rotations_and_reindexings(self):
        result = gate()
        self.assertEqual(result["status"], "pass")
        self.assertEqual(sum(c["rotations"] for c in result["controls"]), 1108)
        self.assertEqual(sum(c["reindexings"] for c in result["controls"]), 48)
        self.assertEqual({c["name"]: c["euler_histogram"].get("2", 0)
                          for c in result["controls"]},
                         {"K4": 2, "parallel3": 2, "K33": 0, "Petersen": 0})

    def test_committed_receipt(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_bounded_rotation_code_gate.json"
        self.assertEqual(json.loads(path.read_text()), gate())

    def test_same_incidence_different_surface(self):
        stars = encode(2, [(0, 1)] * 3)
        self.assertEqual(face_count(*rotation(stars, 3, (False, False))), 1)
        self.assertEqual(face_count(*rotation(stars, 3, (False, True))), 3)

    def test_singleton_cycles_and_empty_permutation(self):
        self.assertEqual(cycle_count([0, 1, 2]), 3)
        self.assertEqual(cycle_count([1, 0, 2]), 2)
        self.assertEqual(cycle_count([]), 0)

    def test_nonpermutations_rejected(self):
        for p in ([0, 0], [0, 2], [-1, 0]):
            with self.assertRaises(ValueError):
                cycle_count(p)

    def test_missing_dart_rejected(self):
        with self.assertRaises(ValueError):
            rotation(((0, 1, 2),), 3, (True,))

    def test_count_without_enumeration(self):
        self.assertEqual([raw_code_count(b) for b in range(4)],
                         [1, 38, 411610900, 37179068599875605])


if __name__ == "__main__":
    unittest.main()
