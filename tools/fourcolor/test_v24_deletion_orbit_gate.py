import itertools
import json
from pathlib import Path
import unittest

from v24_deletion_orbit_gate import (branching_vertices, close, colorings,
                                     components, incidence, orbits, run,
                                     switches, vertex_colorings)
from v24_goldberg import make_goldberg_graph


class DeletionOrbitGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = run()

    def test_independent_enumerators_on_all_four_vertex_graphs(self):
        pairs = list(itertools.combinations(range(4), 2))
        for mask in range(64):
            edges = [e for i, e in enumerate(pairs) if mask >> i & 1]
            self.assertEqual(colorings(4, edges), vertex_colorings(4, edges))

    def test_one_ambient_switch_can_restrict_to_two_small_switches(self):
        ambient = [(0, 1), (1, 2), (2, 3), (3, 4)]
        small = [(0, 1), (3, 4)]
        start, finish = bytes([0, 1]), bytes([1, 0])
        self.assertIn(bytes([1, 0, 1, 0]), switches(incidence(5, ambient), bytes([0, 1, 0, 1])))
        self.assertNotIn(finish, switches(incidence(5, small), start))
        self.assertTrue(any(start in o and finish in o
                            for o in orbits(5, small, colorings(5, small))))

    def test_dodecahedron_orbits_and_joint_minima(self):
        r = self.receipt
        self.assertEqual(r['controls']['dodecahedron']['orbit_sizes'], [6] * 10)
        self.assertEqual(r['deletion_orbit_profiles'], {'[36, 72]': 30})
        self.assertEqual(r['separated_pairs'], 135)
        self.assertEqual(r['unrestricted_zero_pairs'], 135)
        self.assertEqual(r['outcomes'], {'common_agreement': 525,
                                        'positive_nonbranching_minimum': 15})
        self.assertEqual(r['minimum_distances'], {'0': 525, '7': 15})
        self.assertEqual(r['positive_minima_counts'], {'branching': 0, 'nonbranching': 360})
        self.assertEqual(r['fusion_checks'], 210)

    def test_positive_pair_has_nonempty_disjoint_ambient_preimages(self):
        w = self.receipt['first_positive_minimum']
        self.assertEqual(w['left_orbit_size'], 36)
        self.assertEqual(w['right_orbit_size'], 36)
        self.assertEqual(len(w['left_ambient_orbits']), 4)
        self.assertEqual(len(w['right_ambient_orbits']), 4)
        self.assertTrue(set(w['left_ambient_orbits']).isdisjoint(w['right_ambient_orbits']))
        self.assertEqual(self.receipt['extension_profiles'],
                         {'(36, 24, 4)': 30, '(72, 36, 6)': 30})

    def test_literal_fusion_paths_have_correct_endpoints_and_leave_common_graph(self):
        w = self.receipt['first_positive_minimum']
        es = list(map(tuple, make_goldberg_graph(1)['primal_edges']))
        common = list(map(tuple, w['common_edges']))
        self.assertTrue(close(es, w['deleted'][0]).isdisjoint(close(es, w['deleted'][1])))
        self.assertEqual(branching_vertices(20, common, w['left'], w['right']), [])
        for f in w['fusions']:
            seed = common.index(tuple(f['seed']))
            for side, deleted, colors, desired in [
                ('left', w['deleted'][0], w['left'], w['right']),
                ('right', w['deleted'][1], w['right'], w['left']),
            ]:
                ambient = [e for e in es if not set(e) & set(deleted)]
                coloring = w[f'{side}_deletion_coloring']
                path = list(map(tuple, f[side]['path']))
                blocker = common.index(tuple(f[side]['blocker']))
                self.assertEqual(path[0], tuple(f['seed']))
                self.assertEqual(path[-1], tuple(f[side]['blocker']))
                self.assertEqual(colors[blocker], desired[blocker])
                self.assertNotEqual(colors[seed], desired[seed])
                self.assertTrue(any(e not in common for e in path))
                self.assertTrue(all(set(e) & set(g) for e, g in zip(path, path[1:])))
                pair = colors[seed], desired[seed]
                self.assertTrue(all(coloring[ambient.index(e)] in pair for e in path))
                self.assertFalse(any(seed in part and blocker in part
                                     for part in components(incidence(20, common), colors, pair)))

    def test_stored_receipt(self):
        root = Path(__file__).resolve().parents[2]
        expected = json.loads((root / 'results/fourcolor/v24_deletion_orbit_gate.json').read_text())
        self.assertEqual(expected, self.receipt)


if __name__ == '__main__':
    unittest.main()
