import json
from pathlib import Path
import unittest

from v24_bounded_trace_topology_gate import gate, topology


class TraceTopologyTests(unittest.TestCase):
    def test_calibrated_controls_and_reindexings(self):
        result = gate()
        self.assertEqual(result["status"], "pass")
        self.assertEqual(sum(c["reindexings"] for c in result["controls"]), 60)
        self.assertEqual(sum(c["bridges"] for c in result["controls"]), 1)

    def test_committed_receipt(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_bounded_trace_topology_gate.json"
        self.assertEqual(json.loads(path.read_text()), gate())

    def test_empty_is_not_connected(self):
        self.assertEqual(topology((), 0), {"connected": False, "bridges": []})

    def test_one_parallel_edge_deleted_at_a_time(self):
        self.assertEqual(topology(((0, 1, 2), (0, 1, 2)), 3),
                         {"connected": True, "bridges": []})

    def test_repeated_slot_rejected(self):
        with self.assertRaises(ValueError):
            topology(((0, 0, 1), (0, 1, 2)), 3)

    def test_missing_endpoint_rejected(self):
        with self.assertRaises(ValueError):
            topology(((0, 1, 2),), 3)

    def test_bad_edge_indices_rejected(self):
        for star in ((-1, 0, 1), (0, 1, 3)):
            with self.assertRaises(ValueError):
                topology((star, star), 3)


if __name__ == "__main__":
    unittest.main()
