import copy
import json
import unittest
from pathlib import Path

from v24_geodesic_mincut_gate import validate_sphere
from v24_unsplit_cap_sweep_gate import cut, graph, run


class UnsplitCapSweepTests(unittest.TestCase):
    def test_exact_gate_replay(self):
        root = Path(__file__).resolve().parents[2]
        result = json.loads(json.dumps(run()))
        self.assertEqual(result,json.loads((root/'results/fourcolor/v24_unsplit_cap_sweep_gate.json').read_text()))
        self.assertEqual(sum(r['half_cuts'] for r in result['receipts']),70272)
        self.assertEqual([r['minimum_full_width'] for r in result['receipts']],[4,6,6,8,8,10])

    def test_independent_endpoint_formula(self):
        for n in range(3,11):
            g = graph(n)
            expected = set()
            for row in (0,3):
                expected.update(tuple(sorted((row*n+i,row*n+(i+1)%n))) for i in range(n))
            expected.update((r*n+i,(r+1)*n+i) for r in range(3) for i in range(n))
            expected.update(tuple(sorted((2*n+i,n+(i+1)%n))) for i in range(n))
            self.assertEqual(set(map(tuple,g['primal_edges'])),expected)
            self.assertEqual(len(expected),6*n)

    def test_shell_projection_misses_real_ports(self):
        n=8
        edges=graph(n)['primal_edges']
        shell=set(range(n,3*n))
        prefix={v for i in range(n//2) for v in (n+i,2*n+i)}
        internal=[e for e in edges if set(e)<=shell]
        self.assertEqual(len(cut(internal,prefix)),2)
        self.assertEqual(len(cut(edges,prefix)),10)

    def test_splitting_caps_is_not_forbidden_by_the_lower_bound(self):
        for n in (7,9,16,40):
            edges=graph(n)['primal_edges']
            for t in range(1,n):
                side={r*n+i for r in range(4) for i in range(t)}
                self.assertEqual(len(cut(edges,side)),6)

    def test_missing_spoke_breaks_cubic_geometry(self):
        g=copy.deepcopy(graph(5))
        g['primal_edges'].pop(5)
        with self.assertRaises((AssertionError,KeyError,ValueError)):
            validate_sphere(g)


if __name__=='__main__':
    unittest.main()
