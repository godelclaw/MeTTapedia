import copy
import unittest

from v24_absolute_topology_gate import control_graph, run, subdivision, verify_subdivision
from v24_component_copy_gate import proper


class AbsoluteTopologyGate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = run()

    def test_positive_absolute_not_orbit_minima(self):
        self.assertEqual(self.receipt["compared_pairs"], 50544)
        self.assertEqual(self.receipt["absolute_minimizers"], 120)
        self.assertEqual(sorted(r["absolute_minimum"] for r in self.receipt["rows"]),
                         [3, 3, 3, 3, 5, 5])

    def test_all_minima_are_two_spanning_paths(self):
        for row in self.receipt["rows"]:
            self.assertTrue(row["all_components_span_both_ports"])
            for s in row["signatures"]:
                self.assertEqual((s["components"], s["branches"], s["cycle_rank"]), (2, 0, 0))

    def test_saved_witnesses_replay(self):
        n, edges = control_graph()
        for value, witness in self.receipt["witnesses_by_minimum"].items():
            left_edges = [e for e in edges if not set(e) & set(witness["source"])]
            right_edges = [e for e in edges if not set(e) & set(witness["target"])]
            left, right = witness["left_colours"], witness["right_colours"]
            self.assertEqual(len(left), len(left_edges))
            self.assertEqual(len(right), len(right_edges))
            self.assertTrue(proper(n, left_edges, left))
            self.assertTrue(proper(n, right_edges, right))
            common = [e for e in left_edges if e in right_edges]
            actual = [e for e in common if left[left_edges.index(e)] != right[right_edges.index(e)]]
            self.assertEqual(len(actual), int(value))
            self.assertEqual(set(actual), {tuple(e) for part in witness["disagreement_components"]
                                          for e in part})

    def test_subdivision_and_missing_path(self):
        _, edges = control_graph()
        cert = subdivision()
        self.assertTrue(verify_subdivision(edges, cert))
        cert["paths"].pop()
        self.assertFalse(verify_subdivision(edges, cert))

    def test_broken_edge_rejected(self):
        _, edges = control_graph()
        cert = subdivision()
        cert["paths"][0] = [8, 0, 13]
        self.assertFalse(verify_subdivision(edges, cert))

    def test_duplicate_path_rejected(self):
        _, edges = control_graph()
        cert = subdivision()
        cert["paths"][0] = copy.deepcopy(cert["paths"][1])
        self.assertFalse(verify_subdivision(edges, cert))


if __name__ == "__main__":
    unittest.main()
