#!/usr/bin/env python3
"""Test scalar-normalized Count on literal open cubic ladder tangles.

Pre-registered: on monochromatic two-port words, a rung has transition J-I;
n rungs have its nth power. Even lengths 2,4,6,8 have diagonal/off-diagonal
counts (2,1), (6,5), (22,21), (86,85), so their primitive matrices differ
although their supports agree. The planar boundary completion must have
Euler characteristic two with the four terminal ports on one face.
This tests an exact-Count quotient, not the counterexample class.
"""

from collections import Counter
from functools import reduce
import itertools
import json
import math


def ladder(n):
    if n < 1:
        raise ValueError("a physical ladder has at least one rung")
    edges = [(2 * i, 2 * i + 1) for i in range(n)]
    edges += [(2 * i + s, 2 * (i + 1) + s) for i in range(n - 1) for s in range(2)]
    stars = [[] for _ in range(2 * n)]
    for e, (u, v) in enumerate(edges):
        stars[u].append(e)
        stars[v].append(e)
    ports = (0, 1, 2 * n - 2, 2 * n - 1)
    for p, v in enumerate(ports):
        stars[v].append(len(edges) + p)
    assert all(len(s) == 3 for s in stars)
    return edges, ports, stars


def physical_counts(n):
    edges, ports, stars = ladder(n)
    assignment = [-1] * (len(edges) + 4)
    result = Counter()

    def visit(v):
        if v == len(stars):
            result[tuple(assignment[len(edges):])] += 1
            return
        for colors in itertools.permutations(range(3)):
            if any(assignment[e] not in (-1, c) for e, c in zip(stars[v], colors)):
                continue
            changed = [e for e in stars[v] if assignment[e] == -1]
            for e, c in zip(stars[v], colors):
                assignment[e] = c
            visit(v + 1)
            for e in changed:
                assignment[e] = -1

    visit(0)
    return result


def disc_check(n):
    edges, ports, _ = ladder(n)
    term = [2 * n + i for i in range(4)]
    cycle = [term[0], term[2], term[3], term[1]]
    edges = edges + list(zip(ports, term)) + list(zip(cycle, cycle[1:] + cycle[:1]))
    pos = {2 * i + s: (i, 1 if s == 0 else -1) for i in range(n) for s in range(2)}
    pos.update(dict(zip(term, [(-1, 2), (-1, -2), (n, 2), (n, -2)])))
    adj = {v: [] for v in pos}
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    reached, frontier = {0}, [0]
    while frontier:
        for w in adj[frontier.pop()]:
            if w not in reached:
                reached.add(w)
                frontier.append(w)
    assert reached == set(pos)
    rot = {v: sorted(ws, key=lambda w: math.atan2(pos[w][1] - pos[v][1],
                                                  pos[w][0] - pos[v][0]))
           for v, ws in adj.items()}
    unseen = {(u, v) for u in adj for v in adj[u]}
    faces = []
    while unseen:
        dart = next(iter(unseen))
        face = []
        while dart in unseen:
            unseen.remove(dart)
            u, v = dart
            face.append(u)
            dart = (v, rot[v][(rot[v].index(u) + 1) % 3])
        faces.append(face)
    assert len(pos) - len(edges) + len(faces) == 2
    assert any(set(f) == set(term) and len(f) == 4 for f in faces)
    return len(faces)


def multiply(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def gate():
    step = [[int(i != j) for j in range(3)] for i in range(3)]
    power = [[int(i == j) for j in range(3)] for i in range(3)]
    cases = []
    primitive_even = []
    for n in range(1, 9):
        counts = physical_counts(n)
        observed = [[counts[(i, i, j, j)] for j in range(3)] for i in range(3)]
        power = multiply(power, step)
        assert observed == power
        divisor = reduce(math.gcd, (x for row in observed for x in row))
        if n % 2 == 0:
            assert power[0][0] == power[0][1] + 1
            assert divisor == 1
            primitive_even.append(tuple(x // divisor for row in observed for x in row))
            assert all(x > 0 for row in observed for x in row)
        cases.append(dict(rungs=n, vertices=2 * n, diagonal=power[0][0],
                          off_diagonal=power[0][1], full_colorings=sum(counts.values()),
                          completed_faces=disc_check(n)))
    assert len(set(primitive_even)) == 4
    assert [(c["diagonal"], c["off_diagonal"]) for c in cases if c["rungs"] % 2 == 0] == [
        (2, 1), (6, 5), (22, 21), (86, 85)]
    return dict(status="pass", cases=cases,
                scope="Physical planar tangle count normalization; no least-counterexample supplier.")


if __name__ == "__main__":
    print(json.dumps(gate(), sort_keys=True, indent=2))
