import json
import unittest
from pathlib import Path

from v24_path_count_gate import run, check_node


class PathCountTests(unittest.TestCase):
    def test_gate_receipt(self):
        root = Path(__file__).resolve().parents[2]
        self.assertEqual(run(), json.loads((root/'results/fourcolor/v24_path_count_gate.json').read_text()))

    def test_endpoint_bond_is_not_a_node(self):
        edges = [(v, v ^ (1 << b)) for v in range(8) for b in range(3) if v < (v ^ (1 << b))]
        with self.assertRaises(AssertionError):
            check_node(8, edges, {0})

    def test_cube_equator(self):
        edges = [(v, v ^ (1 << b)) for v in range(8) for b in range(3) if v < (v ^ (1 << b))]
        shore, middle = check_node(8, edges, {0, 1, 2, 3})
        self.assertEqual((len(shore), middle), (8, 4))


if __name__ == '__main__':
    unittest.main()
