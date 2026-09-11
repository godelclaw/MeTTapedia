#!/usr/bin/env python3
"""Structural replacement control, not a colouring-configuration search.

Preregistered target: try to distinguish bridge-freeness of two actual
cubic sewings with equal right-side boundary connectivity, face return
and Euler mass. Each internal edge has a unique name occurring twice;
ports have names p0,... and occur once before sewing. Keep parallel edges.
If the target fails, test a finite alternative signature: all realized
boundary bits, selected/unselected-vertex flags and cut size capped at 2.
This is an executable experiment, not a kernel-certified refutation.
"""

from itertools import product
import json

from v24_boundary_connectivity_gate import components
from v24_boundary_rewire_gate import cycles, first_return


def parse(rows):
    assert all(len(row) == 3 for row in rows)
    occurrences = {}
    for v, row in enumerate(rows):
        for i, label in enumerate(row):
            occurrences.setdefault(label, []).append(3 * v + i)
    alpha = list(range(3 * len(rows)))
    edges, ports = [], {}
    for label, ds in occurrences.items():
        if label.startswith('p'):
            assert len(ds) == 1
            ports[int(label[1:])] = ds[0]
        else:
            assert len(ds) == 2
            a, b = ds
            assert a // 3 != b // 3
            alpha[a], alpha[b] = b, a
            edges.append((a // 3, b // 3))
    assert sorted(ports) == list(range(len(ports)))
    rho = tuple(3 * (d // 3) + (d + 1) % 3 for d in range(len(alpha)))
    phi = tuple(rho[a] for a in alpha)
    marks = tuple(ports[i] for i in range(len(ports)))
    vertices = tuple(d // 3 for d in marks)
    labels, count = components(len(rows), edges)
    return dict(n=len(rows), edges=tuple(edges), ports=vertices, marks=marks,
                alpha=alpha, rho=rho, phi=phi, components=count,
                partition=tuple(labels[v] for v in vertices),
                face_return=first_return(phi, marks),
                mass=2 * len(rows) - 2 * len(edges) + 2 * len(cycles(phi)))


def glued(left, right):
    assert len(left['marks']) == len(right['marks'])
    n, offset = left['n'], 3 * left['n']
    alpha = left['alpha'] + [offset + a for a in right['alpha']]
    rho = left['rho'] + tuple(offset + a for a in right['rho'])
    edges = list(left['edges']) + [(n + a, n + b) for a, b in right['edges']]
    for a, b in zip(left['marks'], right['marks']):
        alpha[a], alpha[offset + b] = offset + b, a
        edges.append((a // 3, n + b // 3))
    assert all(alpha[alpha[d]] == d and alpha[d] != d for d in range(len(alpha)))
    nv = left['n'] + right['n']
    count = components(nv, edges)[1]
    bridges = [i for i in range(len(edges))
               if components(nv, edges[:i] + edges[i + 1:])[1] > count]
    faces = len(cycles(tuple(rho[a] for a in alpha)))
    return dict(n=nv, edges=edges, components=count, faces=faces,
                euler=nv - len(edges) + faces, bridges=bridges)


def cut_profile(n, edges, ports):
    """Realized records; flags prevent empty/full cuts from becoming obstructions."""
    result = set()
    for side in product((False, True), repeat=n):
        crossings = sum(side[a] != side[b] for a, b in edges)
        result.add((tuple(side[p] for p in ports), any(side), not all(side), min(2, crossings)))
    return result


def bad_cuts(left, right):
    """The zero/one-edge nontrivial cuts predicted solely by the profiles."""
    result = set()
    for a, ap, an, ac in left:
        for b, bp, bn, bc in right:
            assert len(a) == len(b)
            size = ac + bc + sum(x != y for x, y in zip(a, b))
            if (ap or bp) and (an or bn) and size < 2:
                result.add(size)
    return result


def direct_bad_cuts(n, edges):
    return {sum(side[a] != side[b] for a, b in edges)
            for side in product((False, True), repeat=n)
            if any(side) and not all(side) and sum(side[a] != side[b] for a, b in edges) < 2}


def run():
    exterior = parse((('p0', 'a', 'b'), ('p1', 'b', 'a'),
                      ('p2', 'c', 'd'), ('p3', 'd', 'c')))
    old = parse((('p0', 'p1', 'e'), ('p2', 'p3', 'e')))
    new = parse((('p1', 'p2', 'e'), ('p3', 'p0', 'e')))
    assert old['partition'] == new['partition']
    assert old['face_return'] == new['face_return']
    assert old['mass'] == new['mass'] == 4
    sewn = [glued(exterior, side) for side in (old, new)]
    assert all(g['components'] == 1 and g['euler'] == 2 for g in sewn)
    assert len(sewn[0]['bridges']) == 1 and len(sewn[1]['bridges']) == 0
    profiles = [cut_profile(side['n'], side['edges'], side['ports']) for side in (old, new)]
    context = cut_profile(exterior['n'], exterior['edges'], exterior['ports'])
    assert profiles[0] != profiles[1]
    for g, profile in zip(sewn, profiles):
        assert bad_cuts(context, profile) == direct_bad_cuts(g['n'], g['edges'])
    return dict(schema='fourcolor-structural-bridge-v1',
                scope='Program witness only; no colouring-support equality or kernel refutation asserted.',
                boundary_partition=old['partition'], face_return=old['face_return'], mass=old['mass'],
                composites=[dict(vertices=g['n'], edges=len(g['edges']), components=g['components'],
                                 faces=g['faces'], euler=g['euler'], bridge_count=len(g['bridges']))
                            for g in sewn],
                low_cut_counts=[sorted(bad_cuts(context, p)) for p in profiles])


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
