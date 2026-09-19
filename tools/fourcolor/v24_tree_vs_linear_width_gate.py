#!/usr/bin/env python3
"""Finite witnesses against width-preserving branch-to-linear conversion.

The width supply hands the finite base a rooted branch decomposition of width
at most `w`: a TREE of edge bipartitions whose middle sets -- the vertices
incident to edges on both sides -- have at most `w` vertices.  Only `WidthAtMost`
is required of it; connectivity of shores is supplied separately by the checked
width-preserving connectedization, at the same `w`.

The physical finite-state closure instead processes vertices one at a time.
After a prefix of the vertex order its open interface is the set of edges
leaving that prefix, and the size of that interface is the width indexing the
closure.  Write

    BW = min over branch decompositions of max middle-vertex count
    LP = min over vertex orderings    of max leaving-edge count

This gate checks several finite depths.  In particular it gives a width-four
branch decomposition of a 24-vertex map for which every linear sweep has
width at least six.  The tested depths do not prove that linear width is
unbounded across the family, or rule out a wider bound depending on `w`.

The witness is a tube tree: hexagon nodes joined in a tree by two-edge tubes.
It is simple, cubic, planar and bridgeless, so it lies in the class the base
premise quantifies over, and two-edge-connected, so the connectedization
applies to it.

`BW` is certified by exhibiting one explicit decomposition and measuring it.
Where the search finishes, `LP` is exact: the search over prefixes of interface
at most k either reaches the whole vertex set or exhausts, and exhausting
proves `LP > k`.  A search cap returns an inconclusive result.
"""

from __future__ import annotations

from collections import deque


# --------------------------------------------------------------- the family

def prism(n):
    """C_n x K2: a bridgeless planar cubic control with both widths bounded."""
    edges = []
    for i in range(n):
        edges.append((i, (i + 1) % n))
        edges.append((n + i, n + (i + 1) % n))
        edges.append((i, n + i))
    return edges


def tube_tree(depth):
    """Hexagon nodes in a tree, joined by two-edge tubes.

    Node i owns vertices 6i..6i+5 in a hexagon, each with exactly one external
    end.  Ports are the vertex pairs (0,1), (2,3), (4,5).  The root spends all
    three ports on subtrees; every other node spends port 0 on its parent and
    ports 1 and 2 on its children, capping them if it is a leaf.
    """
    nodes = [0]
    children = {0: []}
    frontier = [(0, p) for p in range(3)]
    for _ in range(depth):
        nxt = []
        for parent, port in frontier:
            idx = len(nodes)
            nodes.append(idx)
            children[idx] = []
            children[parent].append((port, idx))
            nxt.append((idx, 1))
            nxt.append((idx, 2))
        frontier = nxt

    edges = []
    for i in nodes:
        b = 6 * i
        for j in range(6):
            edges.append((b + j, b + (j + 1) % 6))

    def port_vertices(i, p):
        return 6 * i + 2 * p, 6 * i + 2 * p + 1

    for i in nodes:
        for port, child in children[i]:
            a0, a1 = port_vertices(i, port)
            b0, b1 = port_vertices(child, 0)
            edges.append((a0, b0))
            edges.append((a1, b1))
        used = {p for p, _ in children[i]}
        if i != 0:
            used.add(0)
        free = sorted({0, 1, 2} - used)
        if len(free) == 2:
            a0, a1 = port_vertices(i, free[0])
            b0, b1 = port_vertices(i, free[1])
            edges.append((a0, b0))
            edges.append((a1, b1))
        elif len(free) == 3:
            b = 6 * i
            edges += [(b + 0, b + 2), (b + 1, b + 4), (b + 3, b + 5)]
        elif free:
            raise ValueError("unpaired ports")
    return edges, nodes, children


# --------------------------------------------------------------- hypotheses

def vertex_count(edges):
    return len({v for e in edges for v in e})


def is_simple_cubic(edges):
    degree, seen = {}, set()
    for u, v in edges:
        if u == v:
            return False
        key = (min(u, v), max(u, v))
        if key in seen:
            return False
        seen.add(key)
        degree[u] = degree.get(u, 0) + 1
        degree[v] = degree.get(v, 0) + 1
    return all(d == 3 for d in degree.values())


def _connected(edges, n):
    adj = {i: [] for i in range(n)}
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen, stack = {0}, [0]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == n


def is_bridgeless(edges, n):
    """connected, and no single edge disconnects: two-edge-connected"""
    if not _connected(edges, n):
        return False
    return all(_connected(edges[:i] + edges[i + 1:], n) for i in range(len(edges)))


def is_planar(edges):
    """Euler bound plus a Kuratowski check when networkx is present."""
    try:
        import networkx as nx
    except ImportError:
        n, m = vertex_count(edges), len(edges)
        return m <= 3 * n - 6
    graph = nx.Graph()
    graph.add_edges_from(edges)
    return nx.check_planarity(graph)[0]


# ------------------------------------------------------------ the two widths

def middle_card(edges, shore):
    inside, outside = set(), set()
    for i, (u, v) in enumerate(edges):
        (inside if i in shore else outside).update((u, v))
    return len(inside & outside)


def tube_tree_decomposition(edges, nodes, children):
    """One explicit branch decomposition following the tube structure.

    Every edge is assigned to exactly one (node, port) group: the port's two
    hexagon edges, plus the external edges at that port.  A child's subtree
    carries the tube edges up to its parent, so a subtree shore has a
    two-vertex middle.  Groups at a node are combined as a balanced binary
    tree.  Returns every internal shore.
    """
    index = {}
    for i, (u, v) in enumerate(edges):
        index[(min(u, v), max(u, v))] = i

    def key(u, v):
        return index[(min(u, v), max(u, v))]

    parent, parent_port = {}, {}
    for i in nodes:
        for port, child in children[i]:
            parent[child] = i
            parent_port[child] = port

    owner = {}
    for i in nodes:
        b = 6 * i
        for p in range(3):
            owner[key(b + 2 * p, b + 2 * p + 1)] = (i, p)
            owner[key(b + 2 * p + 1, b + (2 * p + 2) % 6)] = (i, p)
    for child in nodes:
        if child in parent:
            i, p = parent[child], parent_port[child]
            owner[key(6 * i + 2 * p, 6 * child)] = (child, 0)
            owner[key(6 * i + 2 * p + 1, 6 * child + 1)] = (child, 0)
    for j, (u, v) in enumerate(edges):
        if j not in owner:
            owner[j] = (u // 6, (u % 6) // 2)

    group = {(i, p): set() for i in nodes for p in range(3)}
    for j, place in owner.items():
        group[place].add(j)

    shores = []

    def combine(parts):
        if len(parts) == 1:
            return parts[0]
        half = len(parts) // 2
        left, right = combine(parts[:half]), combine(parts[half:])
        shores.append(frozenset(left))
        shores.append(frozenset(right))
        return left | right

    def subtree(i):
        kids = dict((p, c) for p, c in children[i])
        parts = []
        for p in range(3):
            block = set(group[(i, p)])
            if p in kids:
                block |= subtree(kids[p])
            if block:
                parts.append(block)
        return combine(parts)

    total = subtree(0)
    assert total == set(range(len(edges))), "decomposition does not cover"
    return [s for s in shores if 0 < len(s) < len(edges)]


def decomposition_width(edges, nodes, children):
    shores = tube_tree_decomposition(edges, nodes, children)
    return max(middle_card(edges, s) for s in shores)


def linear_width_at_most(edges, n, k, cap=8_000_000):
    """exact: some vertex order whose every prefix leaves at most k edges?"""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    full = (1 << n) - 1
    seen = {0}
    queue = deque([(0, 0)])
    explored = 0
    while queue:
        mask, boundary = queue.popleft()
        explored += 1
        if explored > cap:
            return None
        if mask == full:
            return True
        for v in range(n):
            if mask >> v & 1:
                continue
            nxt = mask | (1 << v)
            if nxt in seen:
                continue
            leaving = boundary
            for u in adj[v]:
                leaving += -1 if (mask >> u & 1) else 1
            if leaving <= k:
                seen.add(nxt)
                queue.append((nxt, leaving))
    return False


def linear_width(edges, n, lo=1, hi=16):
    """exact LP, with the largest k whose search exhausted"""
    refuted = None
    for k in range(lo, hi + 1):
        verdict = linear_width_at_most(edges, n, k)
        if verdict is None:
            return None, refuted
        if verdict:
            return k, refuted
        refuted = k
    return None, refuted


# --------------------------------------------------------------------- gate

def run(depths=(0, 1, 2, 3), controls=(4, 6, 8, 10)):
    report = {"control": [], "witness": []}
    for n in controls:
        edges = prism(n)
        nv = vertex_count(edges)
        lp, refuted = linear_width(edges, nv)
        report["control"].append(
            {"name": f"prism C{n}xK2", "vertices": nv, "linear_width": lp,
             "proved_greater_than": refuted})
    for d in depths:
        edges, nodes, children = tube_tree(d)
        nv = vertex_count(edges)
        lp, refuted = linear_width(edges, nv)
        report["witness"].append(
            {"name": f"tube-tree d={d}", "vertices": nv, "nodes": len(nodes),
             "branch_width_at_most": decomposition_width(edges, nodes, children),
             "linear_width": lp, "proved_greater_than": refuted,
             "simple_cubic": is_simple_cubic(edges),
             "bridgeless": is_bridgeless(edges, nv),
             "planar": is_planar(edges)})
    return report


def main():
    report = run()
    print(f"{'family':<18}{'n':>6}{'BW<=':>7}{'LP':>5}{'proved LP>':>12}")
    print("-" * 50)
    for row in report["control"]:
        print(f"{row['name']:<18}{row['vertices']:>6}{'-':>7}"
              f"{row['linear_width']:>5}{row['proved_greater_than']:>12}")
    print()
    for row in report["witness"]:
        print(f"{row['name']:<18}{row['vertices']:>6}"
              f"{row['branch_width_at_most']:>7}{row['linear_width']:>5}"
              f"{row['proved_greater_than']:>12}")
    print()
    for d in (4, 5, 6):
        edges, nodes, children = tube_tree(d)
        print(f"  tube-tree d={d}  n={vertex_count(edges):<5} "
              f"BW<={decomposition_width(edges, nodes, children)}  (LP not attempted)")


if __name__ == "__main__":
    main()
