#!/usr/bin/env python3
"""Generic face-return/rewiring gate, without graph-colouring data.

Preregistered law: compress(p * extend(tau), H) = compress(p, H) * tau.
All nonempty marked sets and all supported transpositions are tested through
six points. Unmarked arc subdivisions test independence from face perimeter.
A separate search tests the weaker cycle-partition-only summary.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def compressed(p, hit):
    index = {x: i for i, x in enumerate(hit)}
    out = []
    for x in hit:
        y = p[x]
        while y not in index:
            y = p[y]
        out.append(index[y])
    return tuple(out)


def partition(p):
    """Independent undirected component calculation, not first-return code."""
    todo = set(range(len(p)))
    blocks = []
    while todo:
        block = {min(todo)}
        while True:
            new = block | {p[x] for x in block} | {x for x in todo if p[x] in block}
            if new == block:
                break
            block = new
        todo -= block
        blocks.append(sorted(block))
    return sorted(blocks)


def transposition(n, i, j):
    result = list(range(n))
    result[i], result[j] = result[j], result[i]
    return tuple(result)


def extend(tau, hit, n):
    result = list(range(n))
    for i, x in enumerate(hit):
        result[x] = hit[tau[i]]
    return tuple(result)


def stretch(p, copies):
    """Replace each arrow by an oriented path, keeping original point names."""
    out = list(p)
    for x, y in enumerate(p):
        path = [x] + list(range(len(out), len(out) + copies)) + [y]
        out.extend([0] * copies)
        for a, b in zip(path, path[1:]):
            out[a] = b
    return tuple(out)


def check(p, hit, tau):
    small = compose(compressed(p, hit), tau)
    large = compose(p, extend(tau, hit, len(p)))
    assert compressed(large, hit) == small
    ambient = partition(large)
    induced = sorted(sorted(hit.index(x) for x in block if x in hit)
                     for block in ambient if any(x in hit for x in block))
    assert induced == partition(small)


def prism_gluing_checks():
    """Physical cubic rotation controls: all cuts of the 3/4-prisms.

Temporarily unpair the full edge boundary. Sew it back with every cyclic
shift of its numbered ports, and compare with the independently built new
edge involution. No planarity of the shifted matching is presumed.
"""
    cases = 0
    for n in (3, 4):
        edges = [(i, (i + 1) % n) for i in range(n)]
        edges += [(n + i, n + (i + 1) % n) for i in range(n)]
        edges += [(i, n + i) for i in range(n)]
        darts = {(u, v): 2 * i for i, (u, v) in enumerate(edges)}
        darts.update({(v, u): 2 * i + 1 for i, (u, v) in enumerate(edges)})
        count = 2 * len(edges)
        alpha = tuple(i ^ 1 for i in range(count))
        rho = [0] * count
        for i in range(n):
            for vertex, neighbours in (
                (i, ((i + 1) % n, (i - 1) % n, n + i)),
                (n + i, (n + (i - 1) % n, n + (i + 1) % n, i)),
            ):
                cycle = [darts[vertex, v] for v in neighbours]
                for a, b in zip(cycle, cycle[1:] + cycle[:1]):
                    rho[a] = b
        assert len(partition(compose(rho, alpha))) == n + 2
        for mask in range(1, (1 << (2 * n)) - 1):
            left = [darts[u, v] for u, v in edges if (mask >> u & 1) and not (mask >> v & 1)]
            left += [darts[v, u] for u, v in edges if (mask >> v & 1) and not (mask >> u & 1)]
            right = [alpha[d] for d in left]
            boundary = set(left + right)
            open_alpha = tuple(d if d in boundary else alpha[d] for d in range(count))
            opened = compose(rho, open_alpha)
            marks = tuple(d for d in range(count) if d not in boundary)[:2]
            hit = tuple(sorted(boundary | set(marks)))
            for shift in range(len(left)):
                sewn_alpha = list(alpha)
                swap = list(range(count))
                for i, l in enumerate(left):
                    r = right[(i + shift) % len(right)]
                    sewn_alpha[l], sewn_alpha[r] = r, l
                    swap[l], swap[r] = r, l
                closed = compose(rho, sewn_alpha)
                assert closed == compose(opened, swap)
                tau = tuple(hit.index(swap[d]) for d in hit)
                check(opened, hit, tau)
                cases += 1
    return cases


def audit():
    counts = []
    for n in range(1, 7):
        checks = 0
        for p in itertools.permutations(range(n)):
            for mask in range(1, 1 << n):
                hit = tuple(x for x in range(n) if mask & (1 << x))
                taus = [tuple(range(len(hit)))]
                taus += [transposition(len(hit), i, j)
                         for i, j in itertools.combinations(range(len(hit)), 2)]
                for tau in taus:
                    check(p, hit, tau)
                    checks += 1
        counts.append(dict(points=n, checks=checks))
    # Cyclic order is deliberately changed while old cofaciality is unchanged.
    p, q, tau = (1, 2, 3, 0), (2, 3, 1, 0), (1, 0, 2, 3)
    assert partition(p) == partition(q)
    assert partition(compose(p, tau)) != partition(compose(q, tau))
    stretched = 0
    for copies in (0, 1, 2, 7, 31, 127):
        for perm in (p, q):
            large = stretch(perm, copies)
            hit = tuple(range(4))
            assert compressed(large, hit) == perm
            for shuffle in itertools.permutations(range(4)):
                check(large, hit, shuffle)
                stretched += 1
    return dict(schema='fourcolor-v24-marked-face-return-v1', exhaustive=counts,
                arc_stretch_checks=stretched, largest_stretched_carrier=512,
                physical_prism_gluing_checks=prism_gluing_checks(),
                partition_counterexample=dict(first=p, second=q, rewire=tau,
                    before=partition(p), after_first=partition(compose(p, tau)),
                    after_second=partition(compose(q, tau))),
                scope='Generic rewiring and physical tangle gluing; no Count supplier asserted.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    receipt = audit()
    # Normalize tuples in the independent replay comparison.
    receipt = json.loads(json.dumps(receipt))
    if args.output:
        atomic_write_json(args.output, receipt)
    if args.check:
        assert receipt == json.loads(args.check.read_text())
    print(json.dumps(receipt, indent=2))
