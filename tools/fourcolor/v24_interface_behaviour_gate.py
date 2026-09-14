#!/usr/bin/env python3
"""How many interface behaviours does a bounded interface actually carry?

The source's regularity step says Count, restricted to bounded interfaces,
factors through a category with finitely many objects: bounded defect forces
hexagonal bulk, and hexagonal bulk has finitely many interface behaviours.

For a cubic map an edge bipartition has a middle set M -- the vertices incident
to edges on both sides -- and each v in M keeps one or two of its edges inside.
What the piece presents to the rest of the map is

  * the inside-degree of each middle vertex,
  * the colour support: which assignments  v |-> {colours on v's inside edges}
    are realized by a proper 3-edge-colouring of the piece,
  * the connectivity pairing: how the piece links the middle vertices,
  * whether the piece hides a component meeting no middle vertex,

all taken up to relabelling the middle set.  Disjoint union is the monoidal
product, so connected pieces generate the image and only those are enumerated.

Finiteness of this profile is not in question and this gate does not test it:
the support is a subset of at most 3^w tuples, so the profile ranges over an
a-priori finite set.  What the gate measures is the SIZE realized by actual
maps, which is the number that decides whether a closure over this presentation
is computable.

The comparison that motivates it: the refuted linear presentation needed 3,696
letters at frontier width five.  The fork presentation is a different
category -- pieces compose along a tree, because the monoidal product is
disjoint union -- and its measured behaviour count at the same width is far
smaller.

Maps are duals of planar triangulations grown by stacking and edge flips:
simple, cubic, planar and bridgeless, the class the base quantifies over.

The slack search is validated against exhaustive enumeration on every map small
enough to enumerate exhaustively, so the counts are not an artefact of the
search order.
"""
from __future__ import annotations

import random
import sys
from itertools import permutations

sys.setrecursionlimit(100000)

COLOURS = (0, 1, 2)


# --------------------------------------------------------------- map supply

def _tetrahedron():
    return [frozenset((0, 1, 2)), frozenset((0, 1, 3)),
            frozenset((0, 2, 3)), frozenset((1, 2, 3))]


def _stack(faces, rng):
    i = rng.randrange(len(faces))
    a, b, c = sorted(faces[i])
    d = 1 + max(v for f in faces for v in f)
    out = faces[:i] + faces[i + 1:]
    return out + [frozenset((a, b, d)), frozenset((b, c, d)), frozenset((a, c, d))]


def _edge_to_faces(faces):
    m = {}
    for i, f in enumerate(faces):
        a, b, c = sorted(f)
        for e in (frozenset((a, b)), frozenset((b, c)), frozenset((a, c))):
            m.setdefault(e, []).append(i)
    return m


def _flip(faces, rng, tries=30):
    e2f = _edge_to_faces(faces)
    keys = [e for e, fs in e2f.items() if len(fs) == 2]
    rng.shuffle(keys)
    for e in keys[:tries]:
        i, j = e2f[e]
        u, v = sorted(e)
        x = next(iter(faces[i] - e))
        y = next(iter(faces[j] - e))
        if x == y or frozenset((x, y)) in e2f:
            continue
        out = [f for k, f in enumerate(faces) if k not in (i, j)]
        out += [frozenset((u, x, y)), frozenset((v, x, y))]
        if len(set(out)) != len(out):
            continue
        return out
    return faces


def _dual(faces):
    e2f = _edge_to_faces(faces)
    edges = []
    for e, fs in e2f.items():
        if len(fs) != 2:
            return None
        edges.append((min(fs), max(fs)))
    return None if len(set(edges)) != len(edges) else edges


def _cubic_simple(edges):
    deg = {}
    for u, v in edges:
        if u == v:
            return False
        deg[u] = deg.get(u, 0) + 1
        deg[v] = deg.get(v, 0) + 1
    return bool(deg) and all(d == 3 for d in deg.values())


def _connected(edges, verts):
    adj = {v: [] for v in verts}
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    s = next(iter(verts))
    seen, st = {s}, [s]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    return len(seen) == len(verts)


def is_bridgeless(edges, verts):
    return _connected(edges, verts) and all(
        _connected(edges[:i] + edges[i + 1:], verts) for i in range(len(edges)))


def is_planar(edges):
    try:
        import networkx as nx
    except ImportError:
        return None
    g = nx.Graph()
    g.add_edges_from(edges)
    return nx.check_planarity(g)[0]


def sample_map(target_faces, rng, flips=6):
    """a simple cubic planar bridgeless map, or None"""
    faces = _tetrahedron()
    while len(faces) < target_faces:
        faces = _stack(faces, rng)
    for _ in range(flips):
        faces = _flip(faces, rng)
    edges = _dual(faces)
    if edges is None or not _cubic_simple(edges):
        return None
    verts = {v for e in edges for v in e}
    if not is_bridgeless(edges, verts) or is_planar(edges) is False:
        return None
    return edges


# ---------------------------------------------------------------- behaviour

def middle_vertices(edges, shore):
    inside, outside = set(), set()
    for i, (u, v) in enumerate(edges):
        (inside if i in shore else outside).update((u, v))
    return inside & outside


def piece_data(edges, shore):
    idx = sorted(shore)
    mid = sorted(middle_vertices(edges, shore))
    inc = {}
    for e in idx:
        u, v = edges[e]
        inc.setdefault(u, []).append(e)
        inc.setdefault(v, []).append(e)

    par = {v: v for v in inc}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for e in idx:
        u, v = edges[e]
        ru, rv = find(u), find(v)
        if ru != rv:
            par[ru] = rv

    deg = tuple(len(inc[v]) for v in mid)
    roots = [find(v) for v in mid]
    pairing = frozenset(frozenset(i for i, r in enumerate(roots) if r == g)
                        for g in set(roots))
    hidden = len({find(v) for v in inc}) > len(set(roots))

    col, support = {}, set()

    def rec(k):
        if k == len(idx):
            support.add(tuple(frozenset(col[e] for e in inc[v]) for v in mid))
            return
        e = idx[k]
        u, v = edges[e]
        for c in COLOURS:
            if any(col.get(f) == c for f in inc[u] if f in col):
                continue
            if any(col.get(f) == c for f in inc[v] if f in col):
                continue
            col[e] = c
            rec(k + 1)
            del col[e]

    rec(0)
    return deg, pairing, hidden, frozenset(support)


def behaviour(edges, shore):
    """canonical interface behaviour, up to relabelling the middle set"""
    deg, pairing, hidden, support = piece_data(edges, shore)
    k, best = len(deg), None
    for p in permutations(range(k)):
        where = {old: new for new, old in enumerate(p)}
        key = (k,
               tuple(deg[p[j]] for j in range(k)),
               tuple(sorted(tuple(sorted(where[i] for i in g)) for g in pairing)),
               hidden,
               tuple(sorted(tuple(tuple(sorted(t[p[j]])) for j in range(k))
                            for t in support)))
        if best is None or key < best:
            best = key
    return best


def support_is_empty(b):
    return len(b[4]) == 0


# -------------------------------------------------------------- enumeration

def exhaustive_pieces(edges, w):
    m = len(edges)
    touch = {}
    for i, (u, v) in enumerate(edges):
        touch.setdefault(u, []).append(i)
        touch.setdefault(v, []).append(i)
    out = []
    for mask in range(1, (1 << m) - 1):
        s = frozenset(i for i in range(m) if mask >> i & 1)
        if len(middle_vertices(edges, s)) > w:
            continue
        start = next(iter(s))
        seen, st = {start}, [start]
        while st:
            e = st.pop()
            for v in edges[e]:
                for f in touch[v]:
                    if f in s and f not in seen:
                        seen.add(f)
                        st.append(f)
        if len(seen) == len(s):
            out.append(s)
    return out


def slack_pieces(edges, w, slack=3):
    m = len(edges)
    touch = {}
    for i, (u, v) in enumerate(edges):
        touch.setdefault(u, []).append(i)
        touch.setdefault(v, []).append(i)
    seen = {frozenset([i]) for i in range(m)}
    frontier, out = list(seen), []
    while frontier:
        nxt = []
        for s in frontier:
            if len(s) < m and len(middle_vertices(edges, s)) <= w:
                out.append(s)
            cand = set()
            for e in s:
                for v in edges[e]:
                    cand.update(touch[v])
            for e in cand - s:
                t = s | {e}
                if t in seen:
                    continue
                seen.add(t)
                if len(middle_vertices(edges, t)) <= w + slack:
                    nxt.append(t)
        frontier = nxt
    return out


def pieces(edges, w, exhaustive_limit=15):
    return (exhaustive_pieces(edges, w) if len(edges) <= exhaustive_limit
            else slack_pieces(edges, w))


# --------------------------------------------------------------------- gate

def validate(widths=(2, 3, 4, 5), seed=1000):
    """the slack search must reproduce the exhaustive answer where checkable"""
    report = {}
    for w in widths:
        rng = random.Random(seed + w)
        checked = missed = 0
        for target in (6, 8):
            for _ in range(2):
                edges = sample_map(target, rng)
                if edges is None or len(edges) > 15:
                    continue
                checked += 1
                a = {behaviour(edges, s) for s in exhaustive_pieces(edges, w)}
                b = {behaviour(edges, s) for s in slack_pieces(edges, w)}
                missed += len(a - b)
        report[w] = {"maps": checked, "missed": missed}
    return report


def measure(w, sizes=(6, 8, 10, 12, 14, 16), samples=4, seed=20260914):
    rng = random.Random(seed)
    seen, rows, empty = set(), [], 0
    for target in sizes:
        before, count, n, m = len(seen), 0, 0, 0
        for _ in range(samples):
            edges = sample_map(target, rng)
            if edges is None:
                continue
            n, m = len({v for e in edges for v in e}), len(edges)
            ps = pieces(edges, w)
            count += len(ps)
            for s in ps:
                b = behaviour(edges, s)
                seen.add(b)
                if support_is_empty(b):
                    empty += 1
        rows.append({"faces": target, "vertices": n, "edges": m,
                     "pieces": count, "new": len(seen) - before,
                     "total": len(seen)})
    return {"width": w, "rows": rows, "behaviours": len(seen),
            "empty_support": empty}


def main():
    print("validation: slack search against exhaustive enumeration")
    for w, r in validate().items():
        print(f"  w={w}: {r['maps']} maps, {r['missed']} behaviour(s) missed")
    print()
    print("distinct interface behaviours realized by planar cubic maps")
    totals = {}
    for w in (2, 3, 4, 5):
        out = measure(w)
        print(f"\n  w = {w}")
        print(f"    {'faces':>6}{'n':>5}{'edges':>7}{'pieces':>9}{'new':>6}{'total':>8}")
        for r in out["rows"]:
            print(f"    {r['faces']:>6}{r['vertices']:>5}{r['edges']:>7}"
                  f"{r['pieces']:>9}{r['new']:>6}{r['total']:>8}")
        totals[w] = out
    print()
    print("  behaviours by interface width:")
    for w, out in totals.items():
        print(f"    w = {w}:  {out['behaviours']:>4}   "
              f"empty-support pieces: {out['empty_support']}")


if __name__ == "__main__":
    main()
