from itertools import product
import json
from pathlib import Path
import unittest

from v24_boundary_connectivity_gate import components, realize, partitions, small_sides
from v24_structural_bridge_gate import bad_cuts, cut_profile, direct_bad_cuts, parse, run


class StructuralBridgeTests(unittest.TestCase):
    def test_spherical_cubic_bridge_witness(self):
        data = run()
        self.assertEqual([g['bridge_count'] for g in data['composites']], [1, 0])
        self.assertEqual([g['euler'] for g in data['composites']], [2, 2])
        self.assertEqual(data['low_cut_counts'], [[1], []])
        receipt = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_structural_bridge_gate.json'
        self.assertEqual(json.loads(json.dumps(data)), json.loads(receipt.read_text()))

    def test_cut_composition_all_small_sides(self):
        cases = 0
        for k in range(5):
            sides = list(small_sides(k)) if k < 4 else [
                realize(p, sub) for p in partitions(4) for sub in (False, True)]
            prepared = [(s, cut_profile(*s)) for s in sides]
            for (n, e, p), a in prepared:
                for (m, f, q), b in prepared:
                    edges = list(e) + [(n + u, n + v) for u, v in f] + [
                        (u, n + v) for u, v in zip(p, q)]
                    count = components(n + m, edges)[1]
                    expected = {0} if count > 1 else set()
                    if any(components(n + m, edges[:i] + edges[i + 1:])[1] > count
                           for i in range(len(edges))):
                        expected.add(1)
                    self.assertEqual(bad_cuts(a, b), expected)
                    cases += 1
        self.assertEqual(cases, 62735)

    def test_nontrivial_flags_and_hidden_components(self):
        self.assertEqual(bad_cuts(cut_profile(0, (), ()), cut_profile(1, (), ())), set())
        self.assertEqual(bad_cuts(cut_profile(1, (), ()), cut_profile(1, (), ())), {0})
        self.assertEqual(bad_cuts(cut_profile(2, (), (0,)), cut_profile(1, (), (0,))), {0, 1})

    def test_parallel_edges_keep_their_multiplicity(self):
        for edges in ((), ((0, 1),), ((0, 1), (0, 1)), ((0, 0), (0, 1))):
            for p in product(range(2), repeat=2):
                profile = cut_profile(2, edges, p)
                # Sewing an edgeless port pair on distinct new vertices
                # provides an independent exhaustive-cut comparison.
                other = cut_profile(2, (), (0, 1))
                sewn = list(edges) + [(p[0], 2), (p[1], 3)]
                self.assertEqual(bad_cuts(profile, other), direct_bad_cuts(4, sewn))

    def test_malformed_presentation_rejected(self):
        for rows in ((('p0', 'x', 'x'),), (('p0', 'p2', 'x'),)):
            with self.assertRaises(AssertionError):
                parse(rows)


if __name__ == '__main__':
    unittest.main()
