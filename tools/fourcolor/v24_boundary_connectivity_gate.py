#!/usr/bin/env python3
"""Preregistered connectivity gate for literal port-to-port multigraph gluing.

Claim: connectivity between seam ports is the equivalence closure of the
two sides' boundary connectivity relations. If every side component has
a port, this also decides connectivity of the whole composite. Test all
simple graphs on at most three vertices with all port assignments through arity
three, and differently sized realizations of every partition at arity four.
Negative controls retain hidden components and distinguish partitions
having equal component counts. No colourings or reducibility data occur.
"""

from itertools import combinations, product
import json


def components(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    labels = [-1] * n
    count = 0
    for root in range(n):
        if labels[root] >= 0:
            continue
        todo = [root]
        while todo:
            v = todo.pop()
            if labels[v] >= 0:
                continue
            labels[v] = count
            todo.extend(adj[v])
        count += 1
    return labels, count


def boundary(n, edges, ports):
    labels, count = components(n, edges)
    marked = tuple(labels[p] for p in ports)
    return marked, count - len(set(marked))


def boundary_join(a, b):
    assert len(a) == len(b)
    # Union-find on ports, independent of the whole-graph BFS above.
    parent = list(range(len(a)))
    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i
    for i in range(len(a)):
        for j in range(i):
            if a[i] == a[j] or b[i] == b[j]:
                parent[root(i)] = root(j)
    labels = tuple(root(i) for i in range(len(a)))
    return labels, len(set(labels))


def sew(left, right):
    n, e, p = left
    m, f, q = right
    assert len(p) == len(q)
    edges = list(e) + [(n + a, n + b) for a, b in f] + [(a, n + b) for a, b in zip(p, q)]
    return components(n + m, edges)


def small_sides(k):
    for n in range(4):
        possible = list(combinations(range(n), 2))
        for bits in product((False, True), repeat=len(possible)):
            edges = tuple(e for e, bit in zip(possible, bits) if bit)
            for ports in product(range(n), repeat=k):
                yield n, edges, ports


def partitions(k):
    if not k:
        yield ()
        return
    for p in partitions(k - 1):
        for a in range(max(p, default=-1) + 2):
            yield p + (a,)


def realize(p, subdivide=False):
    n, edges = len(p), []
    for block in sorted(set(p)):
        members = [i for i, b in enumerate(p) if b == block]
        for a, b in zip(members, members[1:]):
            if subdivide:
                edges.extend(((a, n), (n, b)))
                n += 1
            else:
                edges.append((a, b))
    return n, tuple(edges), tuple(range(len(p)))


def run():
    rows = []
    for k in range(5):
        sides = list(small_sides(k)) if k < 4 else [
            realize(p, sub) for p in partitions(4) for sub in (False, True)]
        prepared = [(s, *boundary(*s)) for s in sides]
        visible, connected, hidden = 0, 0, 0
        for left, a, ah in prepared:
            for right, b, bh in prepared:
                labels, count = sew(left, right)
                join, jc = boundary_join(a, b)
                assert count == jc + ah + bh
                for i, j in product(range(k), repeat=2):
                    assert (labels[left[2][i]] == labels[left[2][j]]) == (join[i] == join[j])
                if ah == bh == 0:
                    assert (count <= 1) == (jc <= 1)
                    visible += 1
                else:
                    hidden += 1
                connected += count == 1
        rows.append(dict(ports=k, sides=len(sides), sewings=len(sides)**2,
                         visible_pairs=visible, hidden_pairs=hidden, connected_sewings=connected))
    return dict(schema='fourcolor-boundary-connectivity-v1', rows=rows,
                scope='Finite structural controls, separate from the universal Lean theorem.')


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
