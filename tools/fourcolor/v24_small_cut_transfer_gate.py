#!/usr/bin/env python3
"""Preregistered open-to-open low-cut transfer gate.

For every pair of small literal multigraphs, sew their middle ports and
retain both outside interfaces. The resulting realized cut profile must
equal the direct profile of the actual sewn graph, not only agree on a
closed acceptance test. Include empty seams, invisible components,
repeated port vertices and saturated cut costs. No colouring catalogue.
"""

from itertools import product
import json

from v24_boundary_connectivity_gate import small_sides
from v24_structural_bridge_gate import cut_profile


def transfer(a, b, left, seam, right):
    result = set()
    for x, xp, xn, xc in a:
        assert len(x) == left + seam
        for y, yp, yn, yc in b:
            assert len(y) == seam + right
            mismatch = sum(u != v for u, v in zip(x[left:], y[:seam]))
            result.add((x[:left] + y[seam:], xp or yp, xn or yn, min(2, xc + yc + mismatch)))
    return result


def sew_open(a, b, left, seam, right):
    n, edges, ports = a
    m, other_edges, other_ports = b
    assert len(ports) == left + seam and len(other_ports) == seam + right
    result_edges = list(edges) + [(n + u, n + v) for u, v in other_edges]
    result_edges += [(u, n + v) for u, v in zip(ports[left:], other_ports[:seam])]
    result_ports = ports[:left] + tuple(n + v for v in other_ports[seam:])
    return n + m, tuple(result_edges), result_ports


def run():
    prepared = {k: [(a, cut_profile(*a)) for a in small_sides(k)] for k in range(4)}
    rows = []
    for left, seam, right in product(range(4), repeat=3):
        if left + seam + right > 3:
            continue
        cases = 0
        for a, ap in prepared[left + seam]:
            for b, bp in prepared[seam + right]:
                actual = cut_profile(*sew_open(a, b, left, seam, right))
                assert transfer(ap, bp, left, seam, right) == actual
                cases += 1
        rows.append(dict(left=left, seam=seam, right=right, sewings=cases))
    return dict(schema='fourcolor-small-cut-transfer-v1', rows=rows,
                scope='Full realized open profiles on literal graph sewings; universal Lean proof separate.')


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
