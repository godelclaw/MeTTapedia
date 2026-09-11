import copy
import json
import unittest
from pathlib import Path

from v24_buffered_shell_gate import IRREGULAR, check_linkage, graph_of_rotation, refine, run
from v24_geodesic_mincut_gate import validate_sphere


class BufferedShellTests(unittest.TestCase):
    def test_full_gate_and_nontrivial_absorption(self):
        root=Path(__file__).resolve().parents[2]
        result=run(json.loads((root/'results/fourcolor/v24_contour_mesh_gate.json').read_text()))
        self.assertEqual(len(result['negative']['complement_components']),3)
        self.assertEqual(sum(r['windows'] for r in result['positive']),1388)
        self.assertEqual(result['positive'][-1]['changed_windows'],12)
        self.assertEqual(result['positive'][-1]['absorbed_vertices'],24)
        self.assertEqual(result,json.loads((root/'results/fourcolor/v24_buffered_shell_gate.json').read_text()))

    def test_refinement_preserves_geometric_calibration(self):
        g=refine(graph_of_rotation(IRREGULAR))
        self.assertEqual(g['primal_vertex_count'],144)
        self.assertEqual(sum(len(f)==5 for f in g['face_cycles']),12)
        self.assertEqual(sum(len(f)==6 for f in g['face_cycles']),62)

    def test_missing_ambient_edge_is_rejected(self):
        g=copy.deepcopy(graph_of_rotation(IRREGULAR))
        g['primal_edges'].pop()
        with self.assertRaises((AssertionError,KeyError,ValueError)):
            validate_sphere(g)

    def test_duplicate_column_is_rejected(self):
        root=Path(__file__).resolve().parents[2]
        specimen=json.loads((root/'results/fourcolor/v24_buffered_shell_gate.json').read_text())['negative']
        paths=copy.deepcopy(specimen['linkage'])
        paths[1]=paths[0]
        with self.assertRaises(AssertionError):
            check_linkage(specimen['graph'],set(specimen['contours'][0]['cycle']),
                          set(specimen['contours'][1]['cycle']),paths,specimen['separator'])


if __name__=='__main__':
    unittest.main()
