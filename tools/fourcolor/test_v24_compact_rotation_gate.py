import itertools
import json
from pathlib import Path
import unittest

from v24_compact_rotation_gate import gate
from v24_bounded_rotation_code_gate import face_count, raw_code_count, rotation
from v24_bounded_trace_topology_gate import topology


class CompactRotationTests(unittest.TestCase):
    def test_pre_registered_tiny_audit(self):
        self.assertEqual(gate()["counts"],
                         dict(raw=3252, valid=145, admissible=72, bad=0))

    def test_receipt(self):
        path = Path(__file__).resolve().parents[2] / "results/fourcolor/v24_compact_rotation_gate.json"
        self.assertEqual(json.loads(path.read_text()), gate())

    def test_carrier_counts(self):
        compact = sum(m ** (3 * n) * 2 ** n for n in range(3) for m in range(4))
        self.assertEqual(compact, 3252)
        self.assertEqual(raw_code_count(2), 411610900)

    def test_arbitrary_local_slot_orders(self):
        for row in itertools.permutations(range(3)):
            stars = [(0, 1, 2), row]
            self.assertEqual(topology(stars, 3), dict(connected=True, bridges=[]))
            faces = []
            for signs in itertools.product((False, True), repeat=2):
                alpha, rho = rotation(stars, 3, signs)
                self.assertTrue(all(alpha[alpha[d]] == d and alpha[d] != d
                                    for d in range(6)))
                faces.append(face_count(alpha, rho))
            self.assertEqual(sorted(faces), [1, 1, 3, 3])


if __name__ == "__main__":
    unittest.main()
