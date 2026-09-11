"""Regression tests for the physical-context coding obstruction."""

from itertools import product
import json
from pathlib import Path
import unittest

from v24_planar_context_code_gate import (
    closed, components, count_colorings, extension_count, find_disc_rotation,
    piece, run,
)


class PhysicalContextGateTests(unittest.TestCase):
    def test_cubic_open_incidence(self):
        for kind in ("A", "B", "T"):
            edges, ports = piece(kind)
            self.assertTrue(all(u != v for u, v in edges))
            for v in range(4):
                self.assertEqual(sum(v in e for e in edges) + ports.count(v), 3)

    def test_all_local_closure_counts_and_bridge_scope(self):
        expected = {("A", "A"): 144, ("B", "A"): 48,
                    ("A", "T"): 0, ("B", "T"): 24}
        for (a, b), count in expected.items():
            result = closed(a, b)
            self.assertEqual(result["colorings"], count)
            self.assertEqual(result["bridges"], [7] if (a, b) == ("A", "T") else [])
            self.assertEqual(result["faces"], 4 + 2 * len(result["components"]))

    def test_crossing_port_order_is_not_a_disc(self):
        edges, _ = piece("A")
        with self.assertRaisesRegex(AssertionError, "ordered disc"):
            find_disc_rotation(edges, [0, 2, 1, 3])

    def test_two_blocks_by_direct_edge_search(self):
        for bits in product((False, True), repeat=2):
            for probe in range(2):
                parts = [closed("B" if b else "A", "T" if j == probe else "A")
                         for j, b in enumerate(bits)]
                edges = [tuple(v + 8 * j for v in e) for j, p in enumerate(parts)
                         for e in p["edges"]]
                count = count_colorings(16, edges)
                self.assertEqual(count, parts[0]["colorings"] * parts[1]["colorings"])
                self.assertEqual(count > 0, bits[probe])
                self.assertEqual(len(components(16, edges)),
                                 sum(len(p["components"]) for p in parts))

    def test_boundary_colour_permutation(self):
        # A cyclic relabelling must preserve the multiplicity, not merely positivity.
        for kind in ("A", "B", "T"):
            for word in product((1, 2, 3), repeat=4):
                relabelled = tuple(c % 3 + 1 for c in word)
                self.assertEqual(extension_count(kind, word), extension_count(kind, relabelled))

    def test_receipt_replay(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_planar_context_code_gate.json"
        self.assertEqual(json.loads(json.dumps(run())), json.loads(path.read_text()))


if __name__ == "__main__":
    unittest.main()
