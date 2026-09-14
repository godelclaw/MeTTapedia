import json
from pathlib import Path
import unittest

from v24_long_face_local_resolution_gate import (
    FOUR_END_PAIRINGS,
    adjacent_two_vertex_profiles,
    run,
)
from v24_positive_face_resolution_gate import face_profile


class LongFaceLocalResolutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = json.loads(json.dumps(run()))

    def test_receipt(self):
        path = (Path(__file__).resolve().parents[2]
                / "results/fourcolor/v24_long_face_local_resolution_gate.json")
        self.assertEqual(self.result, json.loads(path.read_text()))

    def test_three_pairings_are_exhaustive(self):
        normalized = {
            tuple(sorted(tuple(sorted(pair)) for pair in pairing))
            for pairing in FOUR_END_PAIRINGS
        }
        self.assertEqual(len(normalized), 3)
        for pairing in normalized:
            self.assertEqual(sorted(x for pair in pairing for x in pair), list(range(4)))

    def test_each_resolution_has_a_forbidden_word(self):
        for n in range(5, 11):
            target = face_profile(n)
            for profile in adjacent_two_vertex_profiles(n):
                self.assertTrue(set(profile) - set(target))

    def test_common_witness_pattern(self):
        for row in self.result["rows"]:
            witnesses = {tuple(item["bad_word"]) for item in row["resolutions"]}
            self.assertEqual(len(witnesses), 1)
            for item in row["resolutions"]:
                self.assertEqual(item["bad_word_multiplicity"], 1)
                self.assertEqual(item["target_multiplicity"], 0)


if __name__ == "__main__":
    unittest.main()
