#!/usr/bin/env python3
"""Test intrinsic Euler mass on arbitrary actual vertex sides.

Preregistered claim: for a vertex side of a spherical rotation, including
disconnected sides, m = 2V - I + 2F_open = 4 * components. For a proper
side of a connected cubic map each component meets a boundary port, so
0 <= m <= 4 * ports. No connected or coconnected side is required.
Compare direct open face walks to a separate leaf-capped construction.
This is a structural gate, not a colouring or reducibility catalogue.
"""

from itertools import combinations
import json
from random import Random

from v24_vertex_splice_gate import decode, encode_rotation, profile, prism
from v24_boundary_rewire_gate import cycles


def side_data(rot, side):
    side = set(side)
    assert side <= set(range(len(rot)))
    darts = [(v, i) for v in sorted(side) for i in range(3)]
    pos = {d: i for i, d in enumerate(darts)}
    phi, interior = [], 0
    for v, i in darts:
        w = rot[v][i]
        if w in side:
            a, b = w, rot[w].index(v)
            interior += 1
        else:
            a, b = v, i
        phi.append(pos[a, (b + 1) % 3])
    f = len(cycles(phi))
    unseen, components = set(side), []
    while unseen:
        todo, component = [min(unseen)], set()
        while todo:
            v = todo.pop()
            if v in component:
                continue
            component.add(v)
            todo.extend(w for w in rot[v] if w in side and w not in component)
        unseen -= component
        components.append(component)
    ports = len(darts) - interior
    return dict(vertices=len(side), internal_darts=interior, ports=ports,
                open_faces=f, components=len(components), mass=2 * len(side) - interior + 2 * f)


def run():
    controls = [('tetrahedron', [[1, 2, 3], [0, 3, 2], [0, 1, 3], [0, 2, 1]])]
    controls += [(f'prism{m}', prism(m)) for m in (3, 4, 5, 6, 8, 24)]
    rng, rows = Random(991), []
    for name, rot in controls:
        n = len(rot)
        subsets = [s for k in range(n + 1) for s in combinations(range(n), k)] if n <= 12 else [
            tuple(v for v in range(n) if rng.randrange(2)) for _ in range(100)]
        proper, disconnected, largest = 0, 0, 0
        for s in subsets:
            data = side_data(rot, s)
            assert data['mass'] == 4 * data['components']
            if len(s) < n:
                assert 0 <= data['mass'] <= 4 * data['ports']
                proper += 1
            disconnected += data['components'] > 1
            largest = max(largest, data['mass'])
            order = list(s) + [v for v in range(n) if v not in s]
            leaf = profile(*decode(encode_rotation(rot, order)[:len(s)]))
            assert leaf['faces'] == data['open_faces']
            assert 2 * leaf['euler'] == data['mass']
            assert leaf['components'] == data['components']
        rows.append(dict(control=name, sides=len(subsets), proper_sides=proper,
                         disconnected_sides=disconnected, maximum_mass=largest))
    return dict(schema='fourcolor-open-euler-mass-v1', rows=rows,
                scope='Actual planar vertex subsets; universal theorem is a separate proof.')


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
