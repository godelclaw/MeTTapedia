"""Independent small controls for the full-interface ordering diagnostic."""

import itertools
import json
import re
import unittest
from pathlib import Path

from v24_mesh_region_order_gate import audit, bottleneck, brute_force, flood
from v24_mesh_region_order_witness import build


class OrderingControls(unittest.TestCase):
    def test_generated_byte_tables_reproduce_witness(self):
        tables, anchor, full = build()
        source = Path('lean/mettapedia/Mettapedia/GraphTheory/FourColor/'
                      'MeshRegionOrderData.lean').read_text()
        for name, numbers in tables.items():
            pages = re.findall(r'def ' + name + r'Page(\d+) : ByteArray := ByteArray.mk #\[(.*?)\n  \]',
                               source, re.S)
            self.assertEqual([int(i) for i, _ in pages], list(range(len(pages))))
            page_bytes = [bytes(map(int, re.findall(r'\d+', data))) for _, data in pages]
            self.assertTrue(all(len(p) == 256 for p in page_bytes[:-1]))
            metadata = re.search(r'def ' + name + r' : Table where\n  stride := (\d+)\n'
                                 r'  size := (\d+)\n  pages := fun p => match p with\n(.*?)\n\n',
                                 source, re.S)
            self.assertIsNotNone(metadata)
            stride, size = map(int, metadata.group(1, 2))
            selectors = re.findall(r'\| (\d+) => ' + name + r'Page(\d+)', metadata.group(3))
            self.assertEqual([(int(i), int(j)) for i, j in selectors],
                             [(i, i) for i in range(len(pages))])
            packed = b''.join(page_bytes)
            self.assertEqual(len(packed), stride * size)
            self.assertEqual(size, len(numbers))
            self.assertEqual([int.from_bytes(packed[i:i + stride], 'little')
                              for i in range(0, len(packed), stride)], numbers)
        self.assertIn(f'def anchor : Fin 180 := {anchor}\n', source)
        self.assertIn(f'def fullIndex : Cases := {full}\n', source)

    def test_incomplete_population_rejected(self):
        archive = json.loads(Path('results/fourcolor/v24_contour_mesh_gate.json').read_text())
        regions = json.loads(Path('results/fourcolor/v24_mesh_region_gate.json').read_text())
        orders = json.loads(Path('results/fourcolor/v24_ordered_contour_gate.json').read_text())
        archive['receipts'] = archive['receipts'][:-1]
        with self.assertRaises(AssertionError):
            audit(archive, regions, orders)

    def test_complete_small_cost_populations(self):
        # All assignments of two costs or invalidity to the seven nonempty
        # subsets; full permutation search must agree with the recurrence.
        for assignment in itertools.product((None, 1, 3), repeat=7):
            costs = [0, *assignment]
            self.assertEqual(bottleneck(costs, list(range(8)))[0][-1],
                             brute_force(costs, list(range(8)), 3))

    def test_hull_plateaus_are_not_strict_steps(self):
        hulls = [0, 1, 2, 3, 4, 5, 7, 7]
        costs = [0, 1, 1, 1, 1, 1, 1, 1]
        best, parent = bottleneck(costs, hulls)
        self.assertEqual(best[-1], brute_force(costs, hulls, 3))
        self.assertNotEqual(parent[-1], 6)
        hulls = [0, 1, 1, 1]
        self.assertIsNone(bottleneck([0, 1, 1, 1], hulls)[0][-1])
        with self.assertRaises(AssertionError):
            bottleneck([0, 1, 1, 1], [0, 1, 2, 2])

    def test_flood_keeps_only_anchor_component(self):
        self.assertEqual(flood([2, 5, 2], 5, 0), 1)
        self.assertEqual(flood([2, 5, 2], 7, 0), 7)
        with self.assertRaises(AssertionError):
            flood([2, 5, 2], 6, 0)

    def test_witness_and_rank_negative_controls(self):
        tables, anchor, _ = build()
        endpoints = list(zip(tables['edgeNumbers'][::2], tables['edgeNumbers'][1::2]))

        def valid(t, comp, ranks):
            raw = tables['rawMasks'][t]
            marked = lambda mask, v: bool(mask & (1 << v))
            if not marked(comp, anchor) or comp & raw:
                return False
            for v in range(180):
                if not marked(comp, v) or v == anchor:
                    continue
                u, w = endpoints[tables['parentNumbers'][180 * t + v]]
                if v not in (u, w):
                    return False
                parent = w if u == v else u
                if not marked(comp, parent) or ranks[parent] >= ranks[v]:
                    return False
            return all(not marked(comp, u) or marked(raw, v) or marked(comp, v)
                       for e in endpoints for u, v in (e, e[::-1]))

        for t, comp in enumerate(tables['componentMasks']):
            ranks = tables['rankNumbers'][180 * t:180 * (t + 1)]
            self.assertTrue(valid(t, comp, ranks))
            self.assertFalse(valid(t, comp ^ (1 << anchor), ranks))
            self.assertFalse(valid(t, comp, [0] * 180))
            other = next(v for v in range(180) if v != anchor and comp & (1 << v))
            self.assertFalse(valid(t, comp ^ (1 << other), ranks))
            raw_vertex = next(v for v in range(180) if tables['rawMasks'][t] & (1 << v))
            self.assertFalse(valid(t, comp | (1 << raw_vertex), ranks))
            state = tables['stateMasks'][t]
            width = sum(bool(comp & (1 << u)) != bool(comp & (1 << v))
                        for u, v in endpoints)
            if state.bit_count() == 6:
                self.assertGreaterEqual(width, 16)


if __name__ == '__main__':
    unittest.main()
