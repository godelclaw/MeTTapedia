"""Regression controls for transfer-state deletion and rejected weakenings."""

import json
from pathlib import Path
import unittest

from v24_pumping_profile_gate import checked_controls, image, orientation_reversing, run


class PumpingProfileControls(unittest.TestCase):
    def test_swap_changes_acceptance_not_cardinality(self):
        self.assertEqual(run((6,), 1), 2)
        self.assertEqual(run((), 1), 1)
        self.assertEqual(run((6,), 1).bit_count(), run((), 1).bit_count())
        self.assertFalse(run((6,), 1) & 1)
        self.assertTrue(run((), 1) & 1)

    def test_no_spurious_targets(self):
        for relation in range(16):
            self.assertEqual(image(relation, 0), 0)
        for support in range(4):
            self.assertEqual(image(0, support), 0)
            self.assertEqual(image(9, support), support)

    def test_two_swaps_really_are_deletable(self):
        for initial in range(4):
            for suffix in range(16):
                self.assertEqual(run((6, 6, suffix), initial), run((suffix,), initial))

    def test_seam_orientation(self):
        self.assertTrue(orientation_reversing((1, 2, 0), (2, 0, 1), (0, 1, 2)))
        self.assertFalse(orientation_reversing((1, 2, 0), (1, 2, 0), (0, 1, 2)))

    def test_exhaustive_gate(self):
        result = checked_controls()
        self.assertEqual(result["complete_support_runs"], 262144)
        self.assertEqual(result["terminal_context_checks"], 1048576)
        self.assertEqual(result["failures_of_complete_support_deletion"], 0)
        self.assertGreater(result["runs_with_nonempty_final_support"], 0)
        self.assertFalse(result["geometric_supply_established"])

    def test_saved_receipt(self):
        receipt = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_pumping_profile/summary.json"
        with receipt.open() as source:
            self.assertEqual(checked_controls(), json.load(source))


if __name__ == "__main__":
    unittest.main()
