import json
from pathlib import Path
import unittest

from v24_star_attachment_gate import check, run


class StarAttachmentTests(unittest.TestCase):
    def test_receipt_reproduces(self):
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_star_attachment_gate.json'
        self.assertEqual(json.loads(json.dumps(run())), json.loads(receipt.read_text()))

    def test_exhaustive_gate(self):
        result = run()
        self.assertGreater(result["checked"], 5000)
        self.assertGreater(result["multi_component"], 0)
        self.assertGreater(result["repeated_vertices"], 0)

    def test_empty_initial_and_seam(self):
        self.assertEqual(check(0, (), ()), (1, 0, 0))
        self.assertEqual(check(3, ((0, 1),), ()), (3, 0, 2))

    def test_hidden_component_is_retained(self):
        self.assertEqual(check(4, ((0, 1),), (0, 1)), (3, 1, 3))

    def test_distinct_and_repeated_attachments(self):
        self.assertEqual(check(3, (), (0, 1, 2)), (1, 3, 3))
        self.assertEqual(check(3, (), (0, 0, 0)), (3, 1, 3))

    def test_loops_and_parallel_edges(self):
        self.assertEqual(check(2, ((0, 0), (0, 1), (0, 1)), (0, 1)), (1, 1, 1))


if __name__ == "__main__":
    unittest.main()
