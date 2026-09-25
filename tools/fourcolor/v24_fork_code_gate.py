#!/usr/bin/env python3
"""A finite code for the physical fork fold, checked against direct evaluation.

The fork fold in `EdgeShoreFaceForkFold` and `GoertzelV24ForkFold` carries, at
each node of an edge-leaf tree with edge shore S, the realized boundary colour
support, the face-return permutation `ret` on the interface darts, and the
number `closed` of shore faces that miss the interface.  Its carriers depend on
the ambient map, `closed` is an unrestricted natural number, and the fork step
reads the ambient rotation.

This lab tests a proposed finite code for that state.  For a cubic map with
cyclic vertex rotations, write mid(S) for the vertices meeting S and its
complement, and number them 0..n-1.  The code of S is

  deg     the number of S-edges (1 or 2) at each middle vertex;
  colour  the realized boundary colour presentations, per position;
  ret     the face return, carried to positions: every middle vertex v has
          exactly one interface dart d, and d is placed at vert(alpha d) = v;
  defect  min(1, g), where 2g = 2c - |V(S)| + |S| - F(S) is the Euler defect of
          the shore map (c components, F faces);
  cut     every vertex set U of the shore graph crossed by at most one S-edge,
          recorded as (bits on the middle positions, U nonempty,
          complement nonempty, number of crossing edges).

A fork of disjoint shores S and T is described by finitely many local data:
which child positions are the same vertex, one orientation bit at each shared
vertex that stays on the parent interface, and the parent enumeration.  The
abstract fork reads nothing else.  Its face step is the first return of the
merged child returns, multiplied by the product of the swaps at the shared
positions, to the darts kept on the parent interface.

The reference answers are computed directly from each shore: colourings by
exhaustive search, faces by tracing the shore's own face permutation, cuts by
the bridge structure of the shore graph (cross-checked by subset enumeration on
small shores).  None of these uses the abstract fork.

This is a lab.  Agreement on the tested maps is evidence, not a proof; the
controls show which fields are load bearing.  Nothing here enumerates
reducible configurations.
"""

from __future__ import annotations

import itertools
import json
import random
import sys
import time
from collections import defaultdict
from dataclasses import dataclass, field

sys.setrecursionlimit(100000)


# ------------------------------------------------------------------ maps

@dataclass
class RotMap:
    """A loopless cubic rotation map.  Edge i = (u, v) has dart 2i at u and
    dart 2i+1 at v; alpha(d) = d ^ 1; rho is the vertex rotation."""
    nv: int
    edges: list
    rho: list
    name: str = ''

    def vert(self, d):
        return self.edges[d >> 1][d & 1]

    def darts_at(self, v):
        return [d for d in range(2 * len(self.edges)) if self.vert(d) == v]

    def check(self):
        nd = 2 * len(self.edges)
        assert sorted(self.rho) == list(range(nd)), 'rho not a permutation'
        for d in range(nd):
            assert self.vert(self.rho[d]) == self.vert(d), 'rho leaves a vertex'
        for u, v in self.edges:
            assert u != v, 'loop'
        for v in range(self.nv):
            ds = self.darts_at(v)
            assert len(ds) == 3, f'vertex {v} has degree {len(ds)}'
            x = ds[0]
            assert {x, self.rho[x], self.rho[self.rho[x]]} == set(ds), 'rotation not cyclic'
        return self


def phi_cycles(perm, domain):
    seen, cycles = set(), []
    for x in domain:
        if x in seen:
            continue
        cyc, y = [], x
        while y not in seen:
            seen.add(y)
            cyc.append(y)
            y = perm[y]
        cycles.append(cyc)
    return cycles


def genus_of(m: RotMap):
    nd = 2 * len(m.edges)
    phi = {d: m.rho[d ^ 1] for d in range(nd)}
    f = len(phi_cycles(phi, range(nd)))
    c = len(components(m.nv, m.edges, range(len(m.edges))))
    two_g = 2 * c - m.nv + len(m.edges) - f
    return two_g // 2


def components(nv, edges, eids):
    parent = {}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i in eids:
        for v in edges[i]:
            parent.setdefault(v, v)
    for i in eids:
        a, b = find(edges[i][0]), find(edges[i][1])
        if a != b:
            parent[a] = b
    comps = defaultdict(set)
    for v in parent:
        comps[find(v)].add(v)
    return list(comps.values())


def k4():
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    return from_cyclic_orders(4, edges, {0: [1, 2, 3], 1: [0, 3, 2], 2: [0, 1, 3], 3: [0, 2, 1]}, 'K4')


def from_cyclic_orders(nv, edges, orders, name=''):
    """orders[v] = neighbours of v in cyclic order (simple graphs only)."""
    dart = {}
    for i, (u, v) in enumerate(edges):
        dart[(u, v)] = 2 * i
        dart[(v, u)] = 2 * i + 1
    rho = [None] * (2 * len(edges))
    for v, nbrs in orders.items():
        for a, b in zip(nbrs, nbrs[1:] + nbrs[:1]):
            rho[dart[(v, a)]] = dart[(v, b)]
    return RotMap(nv, list(edges), rho, name).check()


def planar_face_chord(m: RotMap, rng):
    """Subdivide two distinct edges on one face and join the new vertices
    across that face.  Preserves cubicity, planarity and bridgelessness."""
    nd = 2 * len(m.edges)
    phi = {d: m.rho[d ^ 1] for d in range(nd)}
    faces = [c for c in phi_cycles(phi, range(nd)) if len({d >> 1 for d in c}) >= 2]
    face = rng.choice(faces)
    while True:
        d1, d2 = rng.sample(face, 2)
        if d1 >> 1 != d2 >> 1:
            break
    return chord(m, d1, d2)


def chord(m: RotMap, d1, d2):
    """Subdivide the edges of darts d1, d2 by new vertices a, b and join a, b.
    The new edge leaves a between the two halves of d1's edge on d1's side of
    the face, and likewise at b; when d1, d2 lie on one face this splits it."""
    e1, e2 = d1 >> 1, d2 >> 1
    if e1 == e2:
        raise ValueError('degenerate chord')
    orders = {}
    for v in range(m.nv):
        x = m.darts_at(v)[0]
        orders[v] = [x, m.rho[x], m.rho[m.rho[x]]]
    edges = list(m.edges)
    ne = len(edges)
    a, b = m.nv, m.nv + 1
    x1, y1 = m.vert(d1), m.vert(d1 ^ 1)
    x2, y2 = m.vert(d2), m.vert(d2 ^ 1)
    edges[e1] = (x1, a) if d1 % 2 == 0 else (a, x1)
    edges[e2] = (x2, b) if d2 % 2 == 0 else (b, x2)
    edges += [(a, y1), (b, y2), (a, b)]
    orders[y1] = [2 * ne + 1 if d == d1 ^ 1 else d for d in orders[y1]]
    orders[y2] = [2 * (ne + 1) + 1 if d == d2 ^ 1 else d for d in orders[y2]]
    orders[a] = [d1 ^ 1, 2 * (ne + 2), 2 * ne]
    orders[b] = [d2 ^ 1, 2 * (ne + 2) + 1, 2 * (ne + 1)]
    rho = [None] * (2 * len(edges))
    for v, ds in orders.items():
        for p, q in zip(ds, ds[1:] + ds[:1]):
            rho[p] = q
    return RotMap(m.nv + 2, edges, rho, m.name + '+').check()


def random_planar(nv, rng):
    m = k4()
    while m.nv < nv:
        m = planar_face_chord(m, rng)
    m.name = f'planar{m.nv}'
    return m


def twist(m: RotMap, vertices):
    rho = list(m.rho)
    for v in vertices:
        ds = m.darts_at(v)
        x = ds[0]
        y, z = m.rho[x], m.rho[m.rho[x]]
        rho[x], rho[z], rho[y] = z, y, x
    return RotMap(m.nv, list(m.edges), rho, m.name + f'~{len(vertices)}').check()


def theta(twisted=False):
    edges = [(0, 1), (0, 1), (0, 1)]
    rho = [None] * 6
    # at 0: darts 0,2,4 ; at 1: darts 1,3,5
    rho[0], rho[2], rho[4] = 2, 4, 0
    if twisted:
        rho[1], rho[3], rho[5] = 3, 5, 1
    else:
        rho[1], rho[5], rho[3] = 5, 3, 1
    return RotMap(2, edges, rho, 'theta' + ('~' if twisted else '')).check()


def petersen(rng):
    outer = [(i, (i + 1) % 5) for i in range(5)]
    inner = [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    spokes = [(i, 5 + i) for i in range(5)]
    edges = outer + inner + spokes
    orders = {}
    for v in range(10):
        nb = [b if a == v else a for a, b in edges if v in (a, b)]
        rng.shuffle(nb)
        orders[v] = nb
    return from_cyclic_orders(10, edges, orders, 'petersen')


def k33(rng):
    edges = [(i, 3 + j) for i in range(3) for j in range(3)]
    orders = {}
    for v in range(6):
        nb = [b if a == v else a for a, b in edges if v in (a, b)]
        rng.shuffle(nb)
        orders[v] = nb
    return from_cyclic_orders(6, edges, orders, 'K33')


def bridged(m1: RotMap, m2: RotMap):
    """Subdivide one edge of each map and join the two new vertices: a
    connected planar cubic map with exactly one bridge."""
    # relabel m2 after m1
    off_v, off_e = m1.nv, len(m1.edges)
    edges = list(m1.edges) + [(u + off_v, v + off_v) for u, v in m2.edges]
    rho = list(m1.rho) + [d + 2 * off_e for d in m2.rho]
    big = RotMap(m1.nv + m2.nv, edges, rho, '')
    # subdivide edge 0 of m1 and edge 0 of m2, join: reuse the chord construction
    # on the disjoint union with darts in different components.
    joined = chord(big, 0, 2 * off_e)
    joined.name = f'bridged{joined.nv}'
    return joined


# ------------------------------------------------------------------ trees

def random_tree(eids, rng):
    eids = list(eids)
    if len(eids) == 1:
        return eids[0]
    rng.shuffle(eids)
    k = rng.randrange(1, len(eids))
    return (random_tree(eids[:k], rng), random_tree(eids[k:], rng))


def connected_tree(m: RotMap, eids, rng):
    """Agglomerate pieces that share a vertex: every shore is connected."""
    pieces = [(e, frozenset(m.edges[e])) for e in eids]
    while len(pieces) > 1:
        pairs = [(i, j) for i in range(len(pieces)) for j in range(i + 1, len(pieces))
                 if pieces[i][1] & pieces[j][1]]
        if not pairs:
            raise ValueError('disconnected edge set')
        i, j = rng.choice(pairs)
        a, b = pieces[i], pieces[j]
        if rng.random() < 0.5:
            a, b = b, a
        merged = ((a[0], b[0]), a[1] | b[1])
        pieces = [p for k, p in enumerate(pieces) if k not in (i, j)] + [merged]
    return pieces[0][0]


def rooted_tree(m: RotMap, rng, connected=True):
    """The consumer's shape: fork (leaf e0) (fork L R).  With `connected`,
    e0 is chosen so that the remaining edges stay connected (a bridge of a
    bridged control is never the root leaf)."""
    choices = list(range(len(m.edges)))
    rng.shuffle(choices)
    for e0 in choices:
        rest = [e for e in range(len(m.edges)) if e != e0]
        if not connected:
            return (e0, random_tree(rest, rng))
        try:
            return (e0, connected_tree(m, rest, rng))
        except ValueError:
            continue
    raise ValueError('no connected rooted tree')


def leaves(t):
    return [t] if isinstance(t, int) else leaves(t[0]) + leaves(t[1])


def forks(t):
    if isinstance(t, int):
        return []
    return forks(t[0]) + forks(t[1]) + [t]


# ------------------------------------------------------------------ direct evaluation

def colourings(m: RotMap, S, limit=None):
    """All proper 3-edge-colourings of the shore S (edges meeting at a vertex
    get distinct colours).  Returns a list of dicts edge -> colour."""
    S = list(S)
    at = defaultdict(list)
    for e in S:
        for v in m.edges[e]:
            at[v].append(e)
    # order edges by BFS for pruning
    order, seen = [], set()
    for s in S:
        if s in seen:
            continue
        queue = [s]
        seen.add(s)
        while queue:
            e = queue.pop(0)
            order.append(e)
            for v in m.edges[e]:
                for f in at[v]:
                    if f not in seen:
                        seen.add(f)
                        queue.append(f)
    out = []
    col = {}

    def rec(i):
        if i == len(order):
            out.append(dict(col))
            return
        e = order[i]
        used = {col[f] for v in m.edges[e] for f in at[v] if f in col}
        for c in range(3):
            if c not in used:
                col[e] = c
                rec(i + 1)
                del col[e]
    rec(0)
    return out


@dataclass
class Direct:
    mid: list
    deg: tuple
    colour: frozenset
    ret: tuple
    defect: int
    genus2: int
    cut: frozenset
    closed: int
    faces: int
    comps: int
    nvs: int


def iface_darts(m, Sset):
    darts = [d for d in range(2 * len(m.edges)) if (d >> 1) in Sset]
    return darts, [d for d in darts if (m.rho[d ^ 1] >> 1) not in Sset]


def shore_face(m, Sset, darts):
    phi = {}
    for d in darts:
        x = m.rho[d ^ 1]
        while (x >> 1) not in Sset:
            x = m.rho[x]
        phi[d] = x
    return phi


def cut_records_direct(m, S, mid):
    """Records (bits on mid, U nonempty, complement nonempty, cost) for all
    U with at most one crossing S-edge, from components and bridges."""
    Sset = set(S)
    verts = sorted({v for e in S for v in m.edges[e]})
    comps = components(m.nv, m.edges, S)
    comp_of = {}
    for i, c in enumerate(comps):
        for v in c:
            comp_of[v] = i
    recs = set()
    k = len(comps)

    def rec_of(U, cost):
        return (tuple(v in U for v in mid), len(U) > 0, len(U) < len(verts), cost)
    # cost 0: unions of components
    for mask in range(1 << k):
        U = set()
        for i in range(k):
            if mask >> i & 1:
                U |= comps[i]
        recs.add(rec_of(U, 0))
    # cost 1: one side of a bridge within one component, plus a union of others
    for e in S:
        rest = [f for f in S if f != e]
        u, v = m.edges[e]
        sub = components(m.nv, m.edges, rest)
        side_u = next((c for c in sub if u in c), {u})
        if v in side_u:
            continue  # not a bridge
        ci = comp_of[u]
        for side in (side_u, comps[ci] - side_u):
            others = [i for i in range(k) if i != ci]
            for mask in range(1 << len(others)):
                U = set(side)
                for t, i in enumerate(others):
                    if mask >> t & 1:
                        U |= comps[i]
                recs.add(rec_of(U, 1))
    return frozenset(recs)


def cut_records_bruteforce(m, S, mid):
    verts = sorted({v for e in S for v in m.edges[e]})
    idx = {v: i for i, v in enumerate(verts)}
    recs = set()
    for mask in range(1 << len(verts)):
        cost = sum(1 for e in S
                   if (mask >> idx[m.edges[e][0]] & 1) != (mask >> idx[m.edges[e][1]] & 1))
        if cost <= 1:
            U = {v for v in verts if mask >> idx[v] & 1}
            recs.add((tuple(v in U for v in mid), len(U) > 0, len(U) < len(verts), cost))
    return frozenset(recs)


def direct(m: RotMap, S, brute_cuts=False):
    Sset = set(S)
    at = defaultdict(int)
    for e in S:
        for v in m.edges[e]:
            at[v] += 1
    verts = sorted(at)
    mid = [v for v in verts if at[v] < 3]
    pos = {v: i for i, v in enumerate(mid)}
    deg = tuple(at[v] for v in mid)
    # colour support
    sup = set()
    for col in colourings(m, S):
        pres = []
        for v in mid:
            pres.append(frozenset(col[e] for e in S if v in m.edges[e]))
        sup.add(tuple(pres))
    # faces and return
    darts, iface = iface_darts(m, Sset)
    phi = shore_face(m, Sset, darts)
    ifset = set(iface)
    by_pos = {}
    for d in iface:
        v = m.vert(d ^ 1)
        assert v in pos and v not in by_pos, 'interface dart not one per middle vertex'
        by_pos[v] = d
    assert len(by_pos) == len(mid)
    ret = []
    for v in mid:
        d = by_pos[v]
        x = phi[d]
        while x not in ifset:
            x = phi[x]
        ret.append(pos[m.vert(x ^ 1)])
    cycles = phi_cycles(phi, darts)
    faces = len(cycles)
    closed = sum(1 for c in cycles if not (set(c) & ifset))
    comps = len(components(m.nv, m.edges, S))
    genus2 = 2 * comps - len(verts) + len(S) - faces
    assert genus2 >= 0 and genus2 % 2 == 0
    cut = cut_records_direct(m, S, mid)
    if brute_cuts:
        assert cut == cut_records_bruteforce(m, S, mid)
    return Direct(mid, deg, frozenset(sup), tuple(ret), min(1, genus2 // 2), genus2,
                  cut, closed, faces, comps, len(verts))


def code(dr: Direct):
    return (dr.deg, dr.colour, dr.ret, dr.defect, dr.cut)


# ------------------------------------------------------------------ descriptor and abstract fork

def descriptor(m: RotMap, S, T):
    """The local gluing data of a physical fork, read off the map."""
    Sset, Tset = set(S), set(T)
    dS, dT = direct_mid(m, S), direct_mid(m, T)
    P = list(S) + list(T)
    dP = direct_mid(m, P)
    posS = {v: i for i, v in enumerate(dS)}
    posT = {v: i for i, v in enumerate(dT)}
    shared = [(posS[v], posT[v]) for v in dS if v in posT]
    orient = {}
    for v in dS:
        if v not in posT:
            continue
        xs = [d for d in m.darts_at(v) if (d >> 1) in Sset]
        xt = [d for d in m.darts_at(v) if (d >> 1) in Tset]
        if len(xs) + len(xt) == 2:
            (x_s,), (x_t,) = xs, xt
            orient[(posS[v], posT[v])] = 'R' if m.rho[x_s] == x_t else 'L'
    order = []
    for v in dP:
        if v in posS and v in posT:
            order.append(('S', posS[v], posT[v]))
        elif v in posS:
            order.append(('L', posS[v]))
        else:
            order.append(('R', posT[v]))
    return (tuple(shared), tuple(sorted(orient.items())), tuple(order))


def direct_mid(m, S):
    at = defaultdict(int)
    for e in S:
        for v in m.edges[e]:
            at[v] += 1
    return sorted(v for v in at if at[v] < 3)


def first_return(perm, keep):
    out = {}
    for x in keep:
        y = perm[x]
        while y not in keep:
            y = perm[y]
        out[x] = y
    return out


def ncycles(perm):
    return len(phi_cycles(perm, list(perm)))


class Illegal(Exception):
    pass


def abstract_fork(cL, cR, desc, *, rewire=True, use_orient=True, components_merged=1,
                  require_shared=True):
    degL, colL, retL, gL, cutL = cL
    degR, colR, retR, gR, cutR = cR
    shared, orient, order = desc
    orient = dict(orient)
    li = [i for i, _ in shared]
    rj = [j for _, j in shared]
    if (require_shared and not shared) or len(set(li)) != len(li) or len(set(rj)) != len(rj):
        raise Illegal('shared positions must form a nonempty partial matching')
    for i, j in shared:
        if degL[i] + degR[j] > 3:
            raise Illegal('degree overflow')
    shL, shR = dict(shared), {j: i for i, j in shared}
    survivors = [('L', i) for i in range(len(degL)) if i not in shL]
    survivors += [('R', j) for j in range(len(degR)) if j not in shR]
    survivors += [('S', i, j) for i, j in shared if degL[i] + degR[j] == 2]
    if sorted(survivors) != sorted(order):
        raise Illegal('parent enumeration is not a bijection onto survivors')
    ppos = {s: k for k, s in enumerate(order)}
    deg = []
    for s in order:
        if s[0] == 'L':
            deg.append(degL[s[1]])
        elif s[0] == 'R':
            deg.append(degR[s[1]])
        else:
            deg.append(2)
    # colour
    col = set()
    for bL in colL:
        for bR in colR:
            if any(bL[i] & bR[j] for i, j in shared):
                continue
            out = []
            for s in order:
                if s[0] == 'L':
                    out.append(bL[s[1]])
                elif s[0] == 'R':
                    out.append(bR[s[1]])
                else:
                    out.append(bL[s[1]] | bR[s[2]])
            col.add(tuple(out))
    # faces
    merged = {('L', i): ('L', retL[i]) for i in range(len(retL))}
    merged.update({('R', j): ('R', retR[j]) for j in range(len(retR))})
    sw = {x: x for x in merged}
    if rewire:
        for i, j in shared:
            sw[('L', i)], sw[('R', j)] = ('R', j), ('L', i)
    p = {x: merged[sw[x]] for x in merged}
    keep = {}
    for s in order:
        if s[0] in 'LR':
            keep[s] = ppos[s]
        else:
            side = orient.get((s[1], s[2]), 'L') if use_orient else 'L'
            keep[('L', s[1]) if side == 'L' else ('R', s[2])] = ppos[s]
    fr = first_return(p, set(keep))
    ret = [None] * len(order)
    for x, k in keep.items():
        ret[k] = keep[fr[x]]
    two_delta = (len(shared) - 2 * components_merged + ncycles(retL_perm(retL))
                 + ncycles(retL_perm(retR)) - ncycles(p))
    if gL or gR:
        g = 1
    else:
        if two_delta < 0 or two_delta % 2:
            raise Illegal(f'negative or odd Euler change {two_delta}')
        g = min(1, two_delta // 2)
    # cuts
    cut = set()
    for rL in cutL:
        for rR in cutR:
            cost = rL[3] + rR[3]
            if cost > 1:
                continue
            if any(rL[0][i] != rR[0][j] for i, j in shared):
                continue
            bits = []
            for s in order:
                if s[0] == 'L':
                    bits.append(rL[0][s[1]])
                elif s[0] == 'R':
                    bits.append(rR[0][s[1]])
                else:
                    bits.append(rL[0][s[1]])
            cut.add((tuple(bits), rL[1] or rR[1], rL[2] or rR[2], cost))
    return (tuple(deg), frozenset(col), tuple(ret), g, frozenset(cut)), two_delta


def retL_perm(ret):
    return {i: ret[i] for i in range(len(ret))}


LEAF = ((1, 1),
        frozenset({(frozenset({c}), frozenset({c})) for c in range(3)}),
        (1, 0), 0,
        frozenset({((False, False), False, True, 0), ((True, False), True, True, 1),
                   ((False, True), True, True, 1), ((True, True), True, False, 0)}))


def root_bad(c):
    """Necessary: no colouring, planar, connected and bridgeless."""
    deg, col, ret, g, cut = c
    assert deg == ()
    small = any(r[1] and r[2] for r in cut)
    return (not col) and g == 0 and not small


# ------------------------------------------------------------------ fold comparison

@dataclass
class Stats:
    maps: int = 0
    trees: int = 0
    forks: int = 0
    leaves: int = 0
    mismatches: list = field(default_factory=list)
    max_width: int = 0


def shore(t):
    return leaves(t)


def check_tree(m, t, stats, brute_cuts=False, nerode=None, connected=True):
    memo = {}

    def dr(node):
        key = tuple(sorted(shore(node)))
        if key not in memo:
            memo[key] = direct(m, key, brute_cuts=brute_cuts)
        return memo[key]
    for e in leaves(t):
        stats.leaves += 1
        d = dr(e)
        if code(d) != LEAF:
            stats.mismatches.append({'map': m.name, 'leaf': e, 'got': repr(code(d))})
    for f in forks(t):
        L, R = f
        dL, dR, dP = dr(L), dr(R), dr(f)
        stats.max_width = max(stats.max_width, len(dP.mid))
        desc = descriptor(m, shore(L), shore(R))
        stats.forks += 1
        merged = dL.comps + dR.comps - dP.comps
        try:
            got, two_delta = abstract_fork(code(dL), code(dR), desc, components_merged=merged,
                                           require_shared=connected)
        except Illegal as exc:
            stats.mismatches.append({'map': m.name, 'fork': repr(f), 'illegal': str(exc)})
            continue
        if got != code(dP):
            stats.mismatches.append({'map': m.name, 'fork': repr(f), 'field': [
                n for n, a, b in zip(('deg', 'colour', 'ret', 'defect', 'cut'), got, code(dP)) if a != b]})
        if dL.genus2 == 0 and dR.genus2 == 0 and two_delta != dP.genus2:
            stats.mismatches.append({'map': m.name, 'fork': repr(f), 'euler': (two_delta, dP.genus2)})
        if dP.genus2 < max(dL.genus2, dR.genus2):
            stats.mismatches.append({'map': m.name, 'fork': repr(f), 'monotone': False})
        if nerode is not None:
            nerode[(code(dL), code(dR), desc)].add(code(dP))
    root = dr(t)
    return root


def run_lab(seed=20260925, n_planar=40, max_nv=16, trees_per_map=6):
    rng = random.Random(seed)
    stats = Stats()
    nerode = defaultdict(set)
    maps = [k4(), theta(), theta(True)]
    for _ in range(n_planar):
        nv = rng.choice(range(6, max_nv + 1, 2))
        maps.append(random_planar(nv, rng))
    base = list(maps[3:])
    for m in base[:15]:
        k = rng.randrange(1, max(2, m.nv // 2))
        maps.append(twist(m, rng.sample(range(m.nv), k)))
    maps.append(petersen(rng))
    maps.append(k33(rng))
    maps.append(bridged(random_planar(6, rng), random_planar(6, rng)))
    maps.append(bridged(k4(), k4()))
    root_rows = []
    for m in maps:
        stats.maps += 1
        g = genus_of(m)
        for t_i in range(trees_per_map):
            connected = t_i % 2 == 0
            try:
                t = rooted_tree(m, rng, connected=connected)
            except ValueError:
                t = rooted_tree(m, rng, connected=False)
            stats.trees += 1
            root = check_tree(m, t, stats, brute_cuts=(m.nv <= 10), nerode=nerode,
                              connected=connected)
            if t_i == 0:
                c = code(root)
                root_rows.append({'map': m.name, 'nv': m.nv, 'genus': g,
                                  'colourable': bool(c[1]), 'defect': c[3],
                                  'small_cut': any(r[1] and r[2] for r in c[4]),
                                  'bad': root_bad(c)})
    collisions = [k for k, v in nerode.items() if len(v) > 1]
    return stats, root_rows, nerode, collisions




# ------------------------------------------------------------------ relabelling

def relabel_code(c, perm):
    """perm[old] = new position."""
    deg, col, ret, g, cut = c
    n = len(deg)
    inv = [None] * n
    for old, new in enumerate(perm):
        inv[new] = old
    deg2 = tuple(deg[inv[k]] for k in range(n))
    col2 = frozenset(tuple(b[inv[k]] for k in range(n)) for b in col)
    ret2 = tuple(perm[ret[inv[k]]] for k in range(n))
    cut2 = frozenset((tuple(r[0][inv[k]] for k in range(n)), r[1], r[2], r[3]) for r in cut)
    return (deg2, col2, ret2, g, cut2)


def relabel_desc(desc, pL, pR, pP):
    shared, orient, order = desc
    shared2 = tuple((pL[i], pR[j]) for i, j in shared)
    orient2 = tuple(sorted(((pL[i], pR[j]), s) for (i, j), s in orient))
    order2 = [None] * len(order)
    for k, s in enumerate(order):
        if s[0] == 'L':
            t = ('L', pL[s[1]])
        elif s[0] == 'R':
            t = ('R', pR[s[1]])
        else:
            t = ('S', pL[s[1]], pR[s[2]])
        order2[pP[k]] = t
    return (shared2, orient2, tuple(order2))


# ------------------------------------------------------------------ controls

def fork_samples(seed=7, n_maps=25, max_nv=14, trees_per_map=4):
    """Physical forks of connected trees: (map, codes, descriptor, parent)."""
    rng = random.Random(seed)
    maps = [k4(), theta(), theta(True), petersen(rng), k33(rng),
            bridged(k4(), k4())]
    for _ in range(n_maps):
        m = random_planar(rng.choice(range(6, max_nv + 1, 2)), rng)
        maps.append(m)
        maps.append(twist(m, rng.sample(range(m.nv), rng.randrange(1, m.nv // 2 + 1))))
    out = []
    for m in maps:
        for _ in range(trees_per_map):
            t = rooted_tree(m, rng, connected=True)
            memo = {}

            def dr(node):
                key = tuple(sorted(shore(node)))
                if key not in memo:
                    memo[key] = direct(m, key)
                return memo[key]
            for f in forks(t):
                L, R = f
                out.append((m.name, dr(L), dr(R), descriptor(m, shore(L), shore(R)), dr(f)))
    return out


def run_controls(seed=7):
    samples = fork_samples(seed)
    result = {'forks': len(samples)}
    # (a) the full code: abstract fork agrees; Nerode classes are singletons
    bad = 0
    for _, dL, dR, desc, dP in samples:
        got, _ = abstract_fork(code(dL), code(dR), desc)
        bad += got != code(dP)
    result['full_code_mismatches'] = bad
    # (b) identity rewire and (c) no orientation bit: detected
    for name, kw in (('identity_rewire', {'rewire': False}), ('no_orientation_bit', {'use_orient': False})):
        miss = 0
        for _, dL, dR, desc, dP in samples:
            try:
                got, _ = abstract_fork(code(dL), code(dR), desc, **kw)
            except Illegal:
                miss += 1
                continue
            miss += got != code(dP)
        result[name + '_mismatches'] = miss
    # (d) Nerode collisions of reduced codes: which fields are load bearing
    def nerode(project, observe):
        classes = defaultdict(set)
        for _, dL, dR, desc, dP in samples:
            classes[(project(code(dL)), project(code(dR)), desc)].add(observe(dP))
        return sum(1 for v in classes.values() if len(v) > 1)
    full = lambda c: c
    result['collisions_full'] = nerode(full, code)
    result['collisions_without_ret'] = nerode(lambda c: (c[0], c[1], c[3], c[4]),
                                              lambda d: (d.defect, d.cut, d.colour))
    result['collisions_ret_cycle_type_only'] = nerode(
        lambda c: (c[0], c[1], tuple(sorted(len(x) for x in phi_cycles(retL_perm(c[2]), range(len(c[2]))))), c[3], c[4]),
        lambda d: (d.defect, d.cut, d.colour))
    result['collisions_without_cut'] = nerode(lambda c: (c[0], c[1], c[2], c[3]),
                                              lambda d: code(d))
    result['collisions_without_defect'] = nerode(lambda c: (c[0], c[1], c[2], c[4]),
                                                 lambda d: code(d))
    # (e) closed is not a function of the code, yet the code determines the parent
    by_code = defaultdict(set)
    for _, dL, dR, desc, dP in samples:
        by_code[code(dP)].add(dP.closed)
    result['codes_with_several_closed_values'] = sum(1 for v in by_code.values() if len(v) > 1)
    result['max_closed'] = max(d.closed for *_, d in samples)
    # (f) relabelling invariance
    rng = random.Random(seed + 1)
    rel = 0
    for _, dL, dR, desc, dP in samples[:2000]:
        nL, nR, nP = len(dL.mid), len(dR.mid), len(dP.mid)
        pL, pR, pP = rng.sample(range(nL), nL), rng.sample(range(nR), nR), rng.sample(range(nP), nP)
        got, _ = abstract_fork(relabel_code(code(dL), pL), relabel_code(code(dR), pR),
                               relabel_desc(desc, pL, pR, pP))
        rel += got != relabel_code(code(dP), pP)
    result['relabelling_failures'] = rel
    # (g) root observations without the cut or defect field
    rows = []
    for m in (bridged(k4(), k4()), petersen(random.Random(3)), twist(k4(), [0])):
        c = code(direct(m, list(range(len(m.edges)))))
        rows.append({'map': m.name, 'genus': genus_of(m), 'bad_full': root_bad(c),
                     'bad_without_cut': (not c[1]) and c[3] == 0,
                     'bad_without_defect': (not c[1]) and not any(r[1] and r[2] for r in c[4])})
    result['roots'] = rows
    return result


# ------------------------------------------------------------------ abstract closure

def canon_key(c):
    deg, col, ret, g, cut = c
    return (deg, tuple(sorted(tuple(tuple(sorted(s)) for s in b) for b in col)), ret, g,
            tuple(sorted(cut)))


def canonical(c):
    n = len(c[0])
    best, best_key = None, None
    for perm in itertools.permutations(range(n)):
        r = relabel_code(c, list(perm))
        k = canon_key(r)
        if best_key is None or k < best_key:
            best, best_key = r, k
    return best


def descriptors(degL, degR, w):
    """All legal fork descriptors with a fixed parent enumeration (the parent
    is canonicalized afterwards)."""
    nL, nR = len(degL), len(degR)
    out = []
    for k in range(1, min(nL, nR) + 1):
        for lefts in itertools.combinations(range(nL), k):
            for rights in itertools.permutations(range(nR), k):
                shared = tuple(zip(lefts, rights))
                if any(degL[i] + degR[j] > 3 for i, j in shared):
                    continue
                open_pairs = [(i, j) for i, j in shared if degL[i] + degR[j] == 2]
                order = [('L', i) for i in range(nL) if i not in lefts]
                order += [('R', j) for j in range(nR) if j not in rights]
                order += [('S', i, j) for i, j in open_pairs]
                if len(order) > w:
                    continue
                for bits in itertools.product('LR', repeat=len(open_pairs)):
                    orient = tuple(sorted(zip(open_pairs, bits)))
                    out.append((shared, orient, tuple(order)))
    return out


def closure(w, prune_defect=True, max_states=200000, time_limit=600):
    """Least set of canonical codes containing the leaf and closed under every
    legal fork with parent interface at most w."""
    t0 = time.time()
    start = canonical(LEAF)
    states = [start]
    index = {canon_key(start): 0}
    roots = set()
    transitions = 0
    pruned = 0
    i = 0
    complete = True
    while i < len(states):
        q = states[i]
        for j in range(i + 1):
            for a, b in ((q, states[j]), (states[j], q)):
                for desc in descriptors(a[0], b[0], w):
                    transitions += 1
                    p, _ = abstract_fork(a, b, desc)
                    if prune_defect and p[3]:
                        pruned += 1
                        continue
                    if len(p[0]) == 0:
                        roots.add(canon_key(p))
                        continue
                    p = canonical(p)
                    k = canon_key(p)
                    if k not in index:
                        index[k] = len(states)
                        states.append(p)
                if len(states) > max_states or time.time() - t0 > time_limit:
                    complete = False
                    break
            if not complete:
                break
        if not complete:
            break
        i += 1
    bad = [r for r in roots if (not r[1]) and r[3] == 0 and not any(x[1] and x[2] for x in r[4])]
    by_n = defaultdict(int)
    for s in states:
        by_n[len(s[0])] += 1
    return {'w': w, 'complete': complete, 'states': len(states), 'by_width': dict(sorted(by_n.items())),
            'roots': len(roots), 'bad_roots': len(bad), 'transitions': transitions,
            'defect_pruned': pruned, 'seconds': round(time.time() - t0, 1)}


# ------------------------------------------------------------------ receipt

LIMITS = {
    'fold_seed': 20260925, 'fold_planar_maps': 40, 'fold_max_vertices': 16,
    'fold_trees_per_map': 6, 'brute_force_cut_check_max_vertices': 10,
    'control_seed': 7, 'closure_widths': [2, 3], 'closure_time_limit_seconds': 600,
}


def closure_roots(w):
    """Root codes of the closure at interface bound w, as (colourable, small cut)."""
    start = canonical(LEAF)
    states, index, roots = [start], {canon_key(start): 0}, set()
    i = 0
    while i < len(states):
        q = states[i]
        for j in range(i + 1):
            for a, b in ((q, states[j]), (states[j], q)):
                for desc in descriptors(a[0], b[0], w):
                    p, _ = abstract_fork(a, b, desc)
                    if p[3]:
                        continue
                    if not p[0]:
                        roots.add((bool(p[1]), any(r[1] and r[2] for r in p[4])))
                        continue
                    p = canonical(p)
                    k = canon_key(p)
                    if k not in index:
                        index[k] = len(states)
                        states.append(p)
        i += 1
    return sorted(roots)


def run():
    stats, rows, nerode, collisions = run_lab(LIMITS['fold_seed'], LIMITS['fold_planar_maps'],
                                              LIMITS['fold_max_vertices'],
                                              LIMITS['fold_trees_per_map'])
    fold = {'maps': stats.maps, 'trees': stats.trees, 'forks': stats.forks,
            'leaves': stats.leaves, 'max_width': stats.max_width,
            'mismatches': len(stats.mismatches), 'nerode_keys': len(nerode),
            'nerode_collisions': len(collisions),
            'nonplanar_roots_with_defect': sum(1 for r in rows if r['genus'] and r['defect']),
            'bridged_roots_with_small_cut': sum(1 for r in rows
                                                if r['map'].startswith('bridged') and r['small_cut']),
            'rejecting_roots': sum(1 for r in rows if r['bad'])}
    closure_out = {}
    for w in LIMITS['closure_widths']:
        c = closure(w, time_limit=LIMITS['closure_time_limit_seconds'])
        c.pop('seconds')
        c['root_codes'] = [{'colourable': a, 'small_cut': b} for a, b in closure_roots(w)]
        closure_out[str(w)] = c
    return {'limits': LIMITS, 'fold': fold, 'controls': run_controls(LIMITS['control_seed']),
            'closure': closure_out}


if __name__ == '__main__':
    print(json.dumps(run(), indent=1, sort_keys=True))

