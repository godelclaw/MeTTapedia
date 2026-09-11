import json
from pathlib import Path
import unittest

from v24_bounded_cubic_trace_gate import assignments, encode, gate


class CubicTraceTests(unittest.TestCase):
    def test_calibrated_controls_and_reindexings(self):
        result = gate()
        self.assertEqual(result["status"], "pass")
        self.assertEqual({c["name"]: c["colourings"] for c in result["controls"]},
                         {"K4": 6, "K33": 12, "Petersen": 0, "bridged": 0})
        self.assertEqual(sum(c["reindexings"] for c in result["controls"]), 48)

    def test_parallel_edges_keep_distinct_indices(self):
        code = encode(2, [(0, 1)] * 3)
        self.assertEqual(code, ((0, 1, 2), (0, 1, 2)))
        self.assertEqual(len(assignments(code, 3)), 6)

    def test_committed_receipt(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_bounded_cubic_trace_gate.json"
        self.assertEqual(json.loads(path.read_text()), gate())

    def test_empty_code_has_empty_assignment(self):
        self.assertEqual(assignments((), 0), {b""})

    def test_loop_rejected(self):
        with self.assertRaises(ValueError):
            encode(1, [(0, 0)])

    def test_noncubic_rejected(self):
        with self.assertRaises(ValueError):
            encode(2, [(0, 1)])

    def test_repeated_slot_rejected(self):
        with self.assertRaises(ValueError):
            assignments(((0, 0, 1), (0, 1, 2)), 3)

    def test_missing_edge_occurrence_rejected(self):
        with self.assertRaises(ValueError):
            assignments(((0, 1, 2),), 3)


if __name__ == "__main__":
    unittest.main()
