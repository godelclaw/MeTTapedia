from itertools import product
import json
from pathlib import Path
import re
import unittest

from v24_deletion_orbit_gate import PAIRS, components, incidence, switches
from v24_pentagon_kempe_plateau_gate import (
    boundary_profile, cycle_profile, proper, run, union_switches, verify_path, word,
)
from v24_pentagon_context_tensor_gate import noncrossing
from v24_plantri_seed_audit import graph_record, parse_ascii_graph
from v24_positive_face_resolution_gate import face_profile


class PentagonKempePlateauTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = run()
        cls.edges = [tuple(e) for e in cls.receipt['edges']]
        cls.ports = cls.receipt['ports']
        cls.path = [bytes(c) for c in cls.receipt['escape_states']]
        cls.target = set(face_profile(5))
        cls.inc = incidence(30, cls.edges)

    def test_receipt(self):
        path = Path(__file__).resolve().parents[2] / 'results/fourcolor/v24_pentagon_kempe_plateau_gate.json'
        self.assertEqual(json.loads(json.dumps(self.receipt)), json.loads(path.read_text()))
        self.assertEqual(self.receipt['colorings'], 354)
        self.assertEqual(self.receipt['distance_histogram'], {'0': 96, '1': 150, '2': 84, '3': 24})
        self.assertEqual(self.receipt['orbits'],
                         [dict(colorings=354, boundary_words=60, extendable_words=30)])

    def test_actual_opened_graph(self):
        graph = graph_record(parse_ascii_graph(self.receipt['ascii_embedding']), 0)
        self.assertEqual(graph['primal_vertex_count'], 30)
        self.assertEqual(len(graph['primal_edges']), 45)
        cap = self.receipt['cap_vertices']
        cycle = {tuple(sorted((cap[i], cap[(i + 1) % 5]))) for i in range(5)}
        self.assertEqual(set(map(tuple, graph['primal_edges'])) - cycle, set(self.edges))
        self.assertEqual({i for i, row in enumerate(self.inc) if len(row) == 1}, set(cap))
        self.assertTrue(all(len(row) == (1 if i in cap else 3) for i, row in enumerate(self.inc)))
        self.assertTrue(all(proper(30, self.edges, c) for c in self.path))

    def test_lean_witness_is_the_same_control(self):
        root = Path(__file__).resolve().parents[2]
        src = (root / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonKempePlateau.lean').read_text()
        ends = src.split('def ends :')[1].split('def ports :')[0]
        self.assertEqual([tuple(map(int, pair)) for pair in re.findall(r'\((\d+),(\d+)\)', ends)],
                         self.edges)
        ports = src.split('def ports :')[1].split('def states :')[0]
        self.assertEqual([int(x) for x in re.search(r'!\[([^]]+)\]', ports)[1].split(',')], self.ports)
        states = src.split('def states :')[1].split('def boundary ')[0]
        parsed = [[int(x) for x in row.split(',')] for row in re.findall(r'=> !\[([^]]+)\]', states)]
        self.assertEqual(parsed, self.receipt['escape_states'])
        steps = src.split('def stepEdges :')[1].split('def selected ')[0]
        parsed = [[int(x) for x in row.split(',')] for row in re.findall(r'=> \[([^]]+)\]', steps)]
        self.assertEqual(parsed, [s['edges'] for s in self.receipt['escape_steps']])

    def test_paths_are_joint_and_cover_every_active_port(self):
        initial = self.path[0]
        for row in self.receipt['matchings']:
            colors = row['colors']
            active = {i for i, e in enumerate(self.ports) if initial[e] in colors}
            ends, used = [], set()
            for path in row['paths']:
                p, q = path['ports']
                es = path['edges']
                self.assertEqual((es[0], es[-1]), (self.ports[p], self.ports[q]))
                self.assertTrue(all(initial[e] in colors for e in es))
                self.assertTrue(all(set(self.edges[e]) & set(self.edges[f]) for e, f in zip(es, es[1:])))
                self.assertFalse(used & set(es))
                used.update(es)
                ends.extend((p, q))
            self.assertEqual(set(ends), active)
            self.assertEqual(len(ends), len(active))
            self.assertTrue(noncrossing([p['ports'] for p in row['paths']]))

    def test_boundary_mask_argument(self):
        # Only 32 boundary masks; no enumeration over forty-edge subsets.
        initial = word(self.path[0], self.ports)
        for row in self.receipt['matchings']:
            a, b = row['colors']
            for bits in product((False, True), repeat=5):
                if any(bits[i] and initial[i] not in (a, b) for i in range(5)):
                    continue
                if any(bits[p['ports'][0]] != bits[p['ports'][1]] for p in row['paths']):
                    continue
                changed = tuple(a + b - c if bits[i] else c for i, c in enumerate(initial))
                self.assertNotIn(changed, self.target)

    def test_component_unions_and_shortest_distance(self):
        initial = self.path[0]
        for colors in PAIRS:
            parts = components(self.inc, initial, colors)
            for bits in product((False, True), repeat=len(parts)):
                selected = {e for part, bit in zip(parts, bits) if bit for e in part}
                c = bytes(sum(colors) - c if e in selected else c for e, c in enumerate(initial))
                self.assertTrue(proper(30, self.edges, c))
                self.assertNotIn(word(c, self.ports), self.target)
        reachable = {initial}
        for _ in range(2):
            reachable |= {d for c in reachable for d in switches(self.inc, c)}
        self.assertTrue(all(word(c, self.ports) not in self.target for c in reachable))
        self.assertEqual(len(self.path), 4)
        self.assertEqual(verify_path(30, self.edges, self.ports, self.path, self.target),
                         self.receipt['escape_steps'])

    def test_corrupt_escape_rejected(self):
        corrupt = [bytearray(c) for c in self.path]
        corrupt[1][0] = (corrupt[1][0] + 1) % 3
        with self.assertRaises(AssertionError):
            verify_path(30, self.edges, self.ports, corrupt, self.target)
        with self.assertRaises(AssertionError):
            verify_path(30, self.edges, self.ports, self.path[:2], self.target)

    def test_joint_profile_is_not_a_reconfiguration_state(self):
        witness = self.receipt['same_profile_witness']
        initial = self.path[0]
        alternative = bytes(witness['alternative'])
        extra = bytes(witness['alternative_successor'])
        self.assertTrue(proper(30, self.edges, alternative))
        self.assertEqual(boundary_profile(self.inc, initial, self.ports),
                         boundary_profile(self.inc, alternative, self.ports))
        self.assertIn(extra, set(switches(self.inc, alternative)))
        self.assertNotIn(boundary_profile(self.inc, extra, self.ports),
                         {boundary_profile(self.inc, c, self.ports) for c in switches(self.inc, initial)})
        reachable = {alternative}
        self.assertNotIn(word(alternative, self.ports), self.target)
        for i in range(2):
            reachable |= {d for c in reachable for d in switches(self.inc, c)}
            self.assertEqual(any(word(c, self.ports) in self.target for c in reachable), i == 1)
        self.assertEqual((witness['initial_distance'], witness['alternative_distance']), (3, 2))
        self.assertEqual((self.receipt['joint_profile_fibres'], self.receipt['mixed_distance_fibres']),
                         (144, 18))
        union_extra = bytes(witness['alternative_union_successor'])
        self.assertIn(union_extra, set(union_switches(self.inc, alternative)))
        self.assertNotIn(boundary_profile(self.inc, union_extra, self.ports),
                         {boundary_profile(self.inc, c, self.ports) for c in union_switches(self.inc, initial)})
        self.assertEqual(witness['union_profile_images'], [8, 8])
        self.assertEqual(witness['union_profile_image_differences'], [4, 4])

    def test_cycle_lengths_do_not_fix_the_compression(self):
        witness = self.receipt['cycle_refinement']
        near, far = bytes(witness['near']), bytes(witness['far'])
        self.assertTrue(all(proper(30, self.edges, c) for c in (near, far)))
        self.assertEqual(cycle_profile(self.inc, near, self.ports), cycle_profile(self.inc, far, self.ports))
        distances = []
        for c in (near, far):
            reachable = {c}
            for i in range(4):
                if any(word(d, self.ports) in self.target for d in reachable):
                    distances.append(i)
                    break
                reachable |= {d for c in reachable for d in switches(self.inc, c)}
        self.assertEqual(distances, witness['distances'])
        self.assertLess(distances[0], distances[1])
        self.assertEqual((witness['profile_fibres'], witness['mixed_distance_fibres']), (192, 6))


if __name__ == '__main__':
    unittest.main()
