#!/usr/bin/env python3
"""Calibrated controls for the literal-tangle / edge-presentation bridge.

Tests B1 (exact factor two), B2 (a free star has zero defect), B3 (sewing
recovers the actual composite), and B4 (defect cannot decrease). These are
generic topology tests, not a graph catalogue or evidence of a global width
bound. Controls distinguish opposite from equal theta rotations, and deliberately
break vertex surjectivity and cyclicity to exercise the bridge's hypotheses.
"""

import json
import random

from v24_topology_viability_gate import component_labels, presentation


def rotation(vertices):
    return tuple(3 * v + (i + 1) % 3 for v in range(vertices) for i in range(3))


def literal_defect(vertices, edges):
    alpha = {d: mate for a, b in edges for d, mate in ((a, b), (b, a))}
    assert len(alpha) == 2 * len(edges), "an internal dart cannot have two mates"
    assert all(a // 3 != b // 3 for a, b in edges)
    todo, faces = set(range(3 * vertices)), 0
    while todo:
        start = at = min(todo)
        faces += 1
        while at in todo:
            todo.remove(at)
            mate = alpha.get(at, at)
            at = 3 * (mate // 3) + (mate % 3 + 1) % 3
        assert at == start
    components = len(set(component_labels(vertices, tuple((a // 3, b // 3) for a, b in edges))))
    mass = 2 * vertices - 2 * len(edges) + 2 * faces
    return 4 * components - mass, mass


def theta(offset=0, twisted=False):
    # Opposite cyclic orders are planar; equal cyclic orders create a handle.
    order = (0, 1, 2) if twisted else (0, 2, 1)
    return tuple((offset + i, offset + 3 + j) for i, j in enumerate(order))


def run(trials=20000):
    assert literal_defect(1, ()) == (0, 4)
    assert literal_defect(2, theta()) == (0, 4)
    assert literal_defect(2, theta(twisted=True)) == (4, 0)
    # The old scratch control used equal orders for every added component.
    # Check the intended planar family and the accidentally constructed family.
    for count in range(1, 5):
        planar = tuple(e for k in range(count) for e in theta(6 * k))
        accidental = theta() + tuple(e for k in range(1, count) for e in theta(6 * k, True))
        assert literal_defect(2 * count, planar) == (0, 4 * count)
        assert literal_defect(2 * count, accidental) == (4 * (count - 1), 4)
    # Neither semantic hypothesis can simply be omitted from the theorem.
    assert 4 * 2 - (2 * 2 + 2 * 1) != 2 * presentation((1, 2, 0), ())[2]
    assert 4 * 1 - (2 * 1 + 2 * 3) != 2 * presentation((0, 1, 2), ())[2]
    rng = random.Random(20260913)
    tested = increments = 0
    for _ in range(trials):
        vertices, edges = 1, ()
        for _ in range(rng.randrange(1, 9)):
            rho = rotation(vertices)
            old = literal_defect(vertices, edges)[0]
            assert old == 2 * presentation(rho, edges)[2]  # B1
            paired = {d for edge in edges for d in edge}
            ports = [d for d in range(3 * vertices) if d not in paired]
            chosen = rng.sample(ports, min(rng.randrange(4), len(ports)))
            seams = tuple((d, 3 * vertices + i) for i, d in enumerate(chosen))
            after_rho = rotation(vertices + 1)
            base_defect = presentation(after_rho, edges)[2]
            full_defect = presentation(after_rho, seams + edges)[2]
            actual = literal_defect(vertices + 1, seams + edges)[0]
            assert 2 * base_defect == old  # B2
            assert 2 * full_defect == actual  # B3
            assert actual >= old  # B4
            assert (actual - old) % 4 == 0
            increments += actual > old
            tested += 1
            vertices, edges = vertices + 1, seams + edges
    return {"trials": trials, "attachment_steps": tested, "handle_creating_steps": increments,
            "bridge_failures": 0, "calibration": "flat/twisted, hidden, unused vertex, split rotation"}


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True))
