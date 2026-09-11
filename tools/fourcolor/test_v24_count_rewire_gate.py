import unittest
from itertools import product
import json
from pathlib import Path

from v24_count_rewire_gate import gate, local_counts


class CountRewireTest(unittest.TestCase):
    def test_all_words(self):
        for word in product(range(4), repeat=4):
            c = local_counts(word)
            self.assertEqual(c["I"] + c["A"], c["H"] + c["B"])
            self.assertEqual(c["Q"], c["A"] + c["B"])

    def test_invalid_boundary(self):
        self.assertEqual(set(local_counts((0, 1, 2, 3)).values()), {0})

    def test_one_zero_branch_does_not_allow_expansion(self):
        c = local_counts((1, 2, 2, 1))
        self.assertEqual((c["A"], c["B"], c["Q"]), (0, 1, 1))

    def test_common_zero_words_are_diagonal(self):
        for w in product(range(1, 4), repeat=4):
            if w[0] ^ w[1] ^ w[2] ^ w[3] == 0:
                c = local_counts(w)
                self.assertEqual(c["I"] == c["H"] == 0, len(set(w)) == 1)

    def test_physical_control(self):
        data = gate()
        self.assertEqual(data["boundary_words_checked"], 256)
        self.assertEqual(data["controls"]["I"]["count"], 0)
        self.assertEqual(data["controls"]["H"]["count"], 24)

    def test_receipt_replay(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_count_rewire_gate.json"
        self.assertEqual(gate(), json.loads(path.read_text()))


if __name__ == "__main__":
    unittest.main()
