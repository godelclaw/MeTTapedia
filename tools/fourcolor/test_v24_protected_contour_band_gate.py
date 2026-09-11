import json
from pathlib import Path
import unittest

from v24_protected_contour_band_gate import band, run, trim


class ProtectedBandTests(unittest.TestCase):
    def test_closed_band_keeps_boundary_and_interior(self):
        incident = [{0, 1}, {1, 2}, {2, 3}, {0}, {3}]
        self.assertEqual(band(incident, {1, 2, 3}, {3}), {0, 1, 2})

    def test_trim_discards_reentry_before_last_outer(self):
        self.assertEqual(trim(list(range(8)), {0, 3}, {6, 7}), [3, 4, 5, 6])

    def test_trim_requires_both_frontiers_in_order(self):
        with self.assertRaises(StopIteration):
            trim([0, 1, 2], {0}, {3})
        with self.assertRaises(ValueError):
            trim([0, 1, 2], {2}, {0})

    def test_spherical_receipts_and_negative_controls(self):
        archive = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_contour_mesh_gate.json"
        result = run(json.loads(archive.read_text()))
        self.assertEqual(len(result["receipts"]), 8)
        self.assertEqual(sum(c["trimmed_paths"] for c in result["receipts"]), 6330)
        self.assertIsNotNone(result["boundary_only_negative"])
        self.assertIsNotNone(result["touching_windows_negative"])
        self.assertTrue(any("2" in c["complement_component_counts"] for c in result["receipts"]))


if __name__ == "__main__":
    unittest.main()
