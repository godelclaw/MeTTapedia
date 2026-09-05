#!/usr/bin/env python3
"""Pentaheptite (haeckelite) tubes as periodic corridors: does the period cell's
transfer relation stabilise?

A thin pentaheptite band is a corridor only when closed into a tube.  Starting
from the (c,0) zigzag tube, one Stone-Wales rotation per 2x2 supercell of
hexagons turns every hexagon into a pentagon or heptagon; the tube then has
period two rings.  The period cell (two rings) is a two-sided slab whose ports
are the edges crossing the ring cuts, ordered canonically.  Its relation R is
computed by search; R^m is iterated until it repeats.

Pre-registered outcomes: P1 index <= width, period 1; P2 finite index, period 1;
P3 eventually periodic with period > 1.  Any outcome gives a finite constant for
excluding long pentaheptite tubes from a least counterexample by the sealed
general periodic-corridor theorem.

Usage: pentaheptite_tube_lab.py [c] [rings]
"""
import sys, math, itertools
from collections import defaultdict, Counter
from defected_tube_sweep_lab import zigzag_tube_rot
from wall_flower_lab import sw_rotate, faces_of


def build(c, h, bond, par):
    """tube with one rotation per supercell: at sites (r, i) with r%2==par[0], i%2==par[1]
    rotate bond type `bond` in {'a','b','x'} (within-ring d-e, within-ring e-d', inter-ring)."""
    n, rot, A, B, vid = zigzag_tube_rot(c, h)
    ring = {}
    for (r, i, s), x in vid.items(): ring[x] = r
    ok = True
    for r in range(1, h - 2):
        if r % 2 != par[0]: continue
        for i in range(c):
            if i % 2 != par[1]: continue
            if bond == 'a': a, b = vid[(r, i, 0)], vid[(r, i, 1)]
            elif bond == 'b': a, b = vid[(r, i, 1)], vid[(r, (i + 1) % c, 0)]
            else: a, b = vid[(r, i, 1)], vid[(r + 1, (i + 1) % c, 0)]
            if not sw_rotate(rot, a, b): ok = False
    return n, rot, ring, vid, ok


def face_sizes(rot, ring, h):
    """sizes of faces whose vertices all lie in rings 2..h-3 (away from the caps)"""
    sizes = []
    for f in faces_of(rot):
        vs = [u for (u, v) in f]
        if all(2 <= ring[v] <= h - 3 for v in vs): sizes.append(len(f))
    return Counter(sizes)


def cell_relation(rot, ring, t):
    """relation of the cell rings {t, t+1}: in-ports = edges (ring t-1, ring t), out-ports =
    edges (ring t+1, ring t+2), ordered by the endpoint in the lower ring then the upper."""
    def ports(rl):
        es = set()
        for u in rot:
            if ring[u] != rl: continue
            for v in rot[u]:
                if ring[v] == rl + 1: es.add((u, v))
        return sorted(es)
    ins, outs = ports(t - 1), ports(t + 1)
    cell = [u for u in rot if ring[u] in (t, t + 1)]
    cellset = set(cell)
    # edges inside the cell and port edges, as unordered keys
    def key(u, v): return (min(u, v), max(u, v))
    inner = set()
    for u in cell:
        for v in rot[u]:
            if v in cellset: inner.add(key(u, v))
    in_keys = [key(u, v) for (u, v) in ins]
    out_keys = [key(u, v) for (u, v) in outs]
    # adjacency restricted: each cell vertex's incident edge keys (inner + ports)
    inc = {u: [key(u, v) for v in rot[u] if v in cellset or key(u, v) in in_keys or key(u, v) in out_keys]
           for u in cell}
    order = sorted(cell, key=lambda u: (ring[u], u))
    width = len(ins)
    words = list(itertools.product(range(3), repeat=width))
    R = {}
    for x in words:
        col = {k: c for k, c in zip(in_keys, x)}
        outsW = set()
        def consistent(u):
            cs = [col[k] for k in inc[u] if k in col]
            return len(cs) == len(set(cs))
        def rec(idx):
            if idx == len(order):
                outsW.add(tuple(col[k] for k in out_keys)); return
            u = order[idx]
            free = [k for k in inc[u] if k not in col]
            used = {col[k] for k in inc[u] if k in col}
            avail = [c for c in range(3) if c not in used]
            if len(avail) < len(free): return
            for perm in itertools.permutations(avail, len(free)):
                for k, cc in zip(free, perm): col[k] = cc
                if all(consistent(w) for k in free for w in k if w in inc):
                    rec(idx + 1)
                for k in free: del col[k]
        if all(consistent(u) for u in order): rec(0)
        R[x] = frozenset(outsW)
    return width, len(outs), words, R


def stabilisation(words, R):
    key = lambda Rel: tuple(Rel[x] for x in words)
    seen = {key(R): 1}; P = R; m = 1
    while True:
        P = {x: frozenset(z for y in P[x] for z in R[y]) for x in words}; m += 1
        k = key(P)
        if k in seen: return seen[k], m - seen[k]
        seen[k] = m


if __name__ == '__main__':
    c = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    h = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    found = None
    for bond in ('a', 'b', 'x'):
        for par in ((0, 0), (0, 1), (1, 0), (1, 1)):
            n, rot, ring, vid, ok = build(c, h, bond, par)
            if not ok: continue
            sizes = face_sizes(rot, ring, h)
            if sizes and set(sizes) <= {5, 7}:
                found = (bond, par, rot, ring, sizes); break
        if found: break
    if not found:
        print("no pentaheptite pattern found among the 12 candidates"); sys.exit(1)
    bond, par, rot, ring, sizes = found
    print(f"c={c}: pattern bond={bond} parity={par}, interior faces {dict(sizes)}")
    t = 4 if 4 % 2 == par[0] else 5
    width, wout, words, R = cell_relation(rot, ring, t)
    nonempty = sum(1 for x in words if R[x])
    idx, per = stabilisation(words, R)
    verdict = 'P1' if (idx <= width and per == 1) else ('P2' if per == 1 else 'P3')
    print(f"cell rings {t},{t+1}: in-width {width}, out-width {wout}, words {len(words)}, "
          f"with a transition {nonempty}; R^m stabilises at index {idx}, period {per} -> {verdict}")
