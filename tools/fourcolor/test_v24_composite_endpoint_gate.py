import json
from pathlib import Path
import unittest

from v24_composite_endpoint_gate import PAIRINGS, gate


class CompositeEndpointTests(unittest.TestCase):
    def test_pairings_complete(self):
        self.assertEqual(len(set(PAIRINGS)), 3)
        for pairs in PAIRINGS:
            self.assertEqual(sorted(p for pair in pairs for p in pair), list(range(4)))

    def test_endpoint_gate(self):
        result = gate()
        self.assertEqual(result["endpoint_cases"], 45)
        for control in result["controls"].values():
            for case in control["cases"]:
                self.assertGreater(case["monochromatic_count"], 0)
                self.assertTrue(all(n > 0 for n in case["completion_counts"]))

    def test_receipt(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_composite_endpoint_gate.json"
        self.assertEqual(gate(), json.loads(path.read_text()))


if __name__ == "__main__":
    unittest.main()
