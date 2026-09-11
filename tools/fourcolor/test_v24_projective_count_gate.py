import itertools
import json
import math
from pathlib import Path
import unittest

from v24_projective_count_gate import disc_check, gate, ladder, physical_counts


class ProjectiveCountTests(unittest.TestCase):
    def test_pre_registered_pairs(self):
        result = gate()
        self.assertEqual([(c["diagonal"], c["off_diagonal"]) for c in result["cases"]
                          if c["rungs"] % 2 == 0], [(2, 1), (6, 5), (22, 21), (86, 85)])

    def test_receipt(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_projective_count_gate.json"
        self.assertEqual(json.loads(path.read_text()), gate())

    def test_same_support_different_primitive_rows(self):
        rows = []
        for n in (2, 4, 6, 8):
            counts = physical_counts(n)
            support = {w[2:] for w, c in counts.items() if w[:2] == (0, 0) and c > 0}
            self.assertEqual(support, {(0, 0), (1, 1), (2, 2)})
            row = tuple(counts[(0, 0, j, j)] for j in range(3))
            self.assertEqual(math.gcd(*row), 1)
            rows.append(row)
        self.assertEqual(len(set(rows)), 4)

    def test_colour_equivariance(self):
        counts = physical_counts(4)
        for p in itertools.permutations(range(3)):
            self.assertEqual({tuple(p[c] for c in w): n for w, n in counts.items()}, counts)

    def test_cubic_incidence_and_terminal_face(self):
        for n in range(1, 9):
            edges, ports, stars = ladder(n)
            self.assertEqual(len(stars), 2 * n)
            self.assertEqual(len(edges), 3 * n - 2)
            self.assertTrue(all(len(set(s)) == 3 for s in stars))
            self.assertEqual(len(ports), 4)
            self.assertEqual(disc_check(n), n + 4)

    def test_no_empty_physical_rung(self):
        with self.assertRaises(ValueError):
            ladder(0)


if __name__ == "__main__":
    unittest.main()
