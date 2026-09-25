#!/usr/bin/env python3
"""Realize the abstract fork-code closure by actual planar pieces, fork by fork.

Soundness of the closure `Reach w` means: every code of the closure is the code
of a connected shore of a planar cubic map.  This lab builds the witnesses
along the closure's own derivation.

* An open piece is a connected graph whose vertices carry a cyclic order of
  three slots, each holding a dart of the piece or left open.
* The leaf is one edge with two open slots at each end.
* A fork glues two witness pieces at the vertices the descriptor pairs: at a
  vertex where both pieces have one edge the new dart goes before or after the
  other one, which is the orientation choice; otherwise it fills the open slot.
* A piece is closed into a planar cubic map by capping each face that contains
  open slots: a ring of new vertices, one per slot, joined to the slots in
  order (a lollipop when the face has one slot).  Capping keeps the Euler
  characteristic, so the map is planar exactly when the piece is.

The code of the witness is computed directly from the capped map (the lab's
`direct`), never from the abstract fork, and compared with the closure state up
to renaming.  A state whose realization fails is reported with its derivation.

Usage: realize_compositional.py W [--max-states N]
"""
import argparse
import itertools
import json
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import v24_fork_code_gate as lab  # noqa: E402


class Piece:
    def __init__(self, nv, edges, rot):
        self.nv, self.edges, self.rot = nv, list(edges), [list(r) for r in rot]

    def ndarts(self):
        return 2 * len(self.edges)


def leaf_piece():
    return Piece(2, [(0, 1)], [[0, None, None], [1, None, None]])


def glue(P1, P2, pairs, orient):
    """pairs: list of (v1, v2); orient[(v1, v2)] in 'LR' at one-plus-one vertices."""
    off = P1.ndarts()
    match2 = {v2: v1 for v1, v2 in pairs}
    vmap2, nv = {}, P1.nv
    for v in range(P2.nv):
        if v in match2:
            vmap2[v] = match2[v]
        else:
            vmap2[v] = nv
            nv += 1
    edges = list(P1.edges) + [(vmap2[u], vmap2[v]) for u, v in P2.edges]
    rot = [list(r) for r in P1.rot] + [None] * (nv - P1.nv)
    for v in range(P2.nv):
        r2 = [None if x is None else x + off for x in P2.rot[v]]
        if v not in match2:
            rot[vmap2[v]] = r2
            continue
        v1 = match2[v]
        r1 = rot[v1]
        d1 = [x for x in r1 if x is not None]
        d2 = [x for x in r2 if x is not None]
        if len(d1) + len(d2) > 3:
            return None
        if len(d1) == 2:
            rot[v1] = [x if x is not None else d2[0] for x in r1]
        elif len(d2) == 2:
            rot[v1] = [x if x is not None else d1[0] for x in r2]
        else:
            a, b = d1[0], d2[0]
            rot[v1] = [a, b, None] if orient[(v1, v)] == 'R' else [a, None, b]
    return Piece(nv, edges, rot)


def cap(P):
    """Close a planar piece into a cubic map; the piece's edges keep their ids."""
    edges = list(P.edges)
    ne = len(edges)
    where = {}
    for v in range(P.nv):
        for k, x in enumerate(P.rot[v]):
            if x is not None:
                where[x] = (v, k)
    phi, corner = {}, {}
    for d in range(2 * ne):
        v, k = where[d ^ 1]
        slots = []
        while True:
            k = (k + 1) % 3
            x = P.rot[v][k]
            if x is None:
                slots.append((v, k))
            else:
                break
        phi[d], corner[d] = x, slots
    faces = lab.phi_cycles(phi, range(2 * ne))
    new_edges = list(edges)
    stub, grot = {}, {}
    nvx = P.nv

    def add(u, w):
        new_edges.append((u, w))
        e = len(new_edges) - 1
        return 2 * e, 2 * e + 1
    for f in faces:
        slots = [s for d in f for s in corner[d]]
        k = len(slots)
        if k == 0:
            continue
        if k >= 2:
            rs = list(range(nvx, nvx + k))
            nvx += k
            t = []
            for i, (v, kk) in enumerate(slots):
                dv, dr = add(v, rs[i])
                stub[(v, kk)] = dv
                t.append(dr)
            fwd, bwd = [None] * k, [None] * k
            for i in range(k):
                x, y = add(rs[i], rs[(i + 1) % k])
                fwd[i], bwd[(i + 1) % k] = x, y
            for i in range(k):
                grot[rs[i]] = [t[i], bwd[i], fwd[i]]
        else:
            (v, kk), = slots
            r, a, b = nvx, nvx + 1, nvx + 2
            nvx += 3
            dv, dr = add(v, r)
            stub[(v, kk)] = dv
            ra_r, ra_a = add(r, a)
            rb_r, rb_b = add(r, b)
            x1a, x1b = add(a, b)
            x2a, x2b = add(a, b)
            grot[r] = [dr, ra_r, rb_r]
            grot[a] = [ra_a, x1a, x2a]
            grot[b] = [rb_b, x2b, x1b]
    rho = [None] * (2 * len(new_edges))
    for v in range(P.nv):
        ds = [x if x is not None else stub[(v, k)] for k, x in enumerate(P.rot[v])]
        for p, q in zip(ds, ds[1:] + ds[:1]):
            rho[p] = q
    for v, ds in grot.items():
        for p, q in zip(ds, ds[1:] + ds[:1]):
            rho[p] = q
    m = lab.RotMap(nvx, new_edges, rho, 'capped').check()
    return m, list(range(ne))


def piece_code(P):
    m, S = cap(P)
    if lab.genus_of(m) != 0:
        return None, None, m
    d = lab.direct(m, S)
    return lab.code(d), d.mid, m


def perm_to(c, target_key):
    n = len(c[0])
    for perm in itertools.permutations(range(n)):
        r = lab.relabel_code(c, list(perm))
        if lab.canon_key(r) == target_key:
            return list(perm)
    return None


def closure_with_derivations(w, max_states):
    start = lab.canonical(lab.LEAF)
    states, index, deriv = [start], {lab.canon_key(start): 0}, [None]
    roots = {}
    i = 0
    while i < len(states) and len(states) <= max_states:
        q = states[i]
        for j in range(i + 1):
            for (a, ia), (b, ib) in (((q, i), (states[j], j)), ((states[j], j), (q, i))):
                for desc in lab.descriptors(a[0], b[0], w):
                    p, _ = lab.abstract_fork(a, b, desc)
                    if p[3]:
                        continue
                    if not p[0]:
                        k = lab.canon_key(p)
                        if k not in roots:
                            roots[k] = (p, ia, ib, desc)
                        continue
                    pc = lab.canonical(p)
                    k = lab.canon_key(pc)
                    if k not in index:
                        index[k] = len(states)
                        states.append(pc)
                        deriv.append((ia, ib, desc, p))
        i += 1
    return states, deriv, roots


def realize_fork(Wa, Wb, desc, target_key):
    """Glue witnesses Wa=(P, mid, perm) and Wb along desc; try all orientations."""
    Pa, mida, perma = Wa
    Pb, midb, permb = Wb
    inva = {new: old for old, new in enumerate(perma)}
    invb = {new: old for old, new in enumerate(permb)}
    shared, _, _ = desc
    pairs = [(mida[inva[i]], midb[invb[j]]) for i, j in shared]
    ones = []
    for v1, v2 in pairs:
        k1 = sum(1 for x in Pa.rot[v1] if x is not None)
        k2 = sum(1 for x in Pb.rot[v2] if x is not None)
        if k1 + k2 == 2:
            ones.append((v1, v2))
    for bits in itertools.product('LR', repeat=len(ones)):
        P = glue(Pa, Pb, pairs, dict(zip(ones, bits)))
        if P is None:
            continue
        c, mid, m = piece_code(P)
        if c is None:
            continue
        if not mid:
            if lab.canon_key(c) == target_key:
                return P, mid, []
            continue
        perm = perm_to(c, target_key)
        if perm is not None:
            return P, mid, perm
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('w', type=int)
    ap.add_argument('--max-states', type=int, default=100000)
    args = ap.parse_args()
    t0 = time.time()
    states, deriv, roots = closure_with_derivations(args.w, args.max_states)
    t1 = time.time()
    wit = []
    c, mid, _ = piece_code(leaf_piece())
    wit.append((leaf_piece(), mid, perm_to(c, lab.canon_key(states[0]))))
    assert wit[0][2] is not None, 'leaf not realized'
    failures = []
    for s in range(1, len(states)):
        ia, ib, desc, p = deriv[s]
        r = realize_fork(wit[ia], wit[ib], desc, lab.canon_key(states[s]))
        if r is None:
            failures.append({'state': s, 'from': [ia, ib], 'desc': repr(desc)})
            wit.append(None)
            break
        wit.append(r)
    root_fail = []
    if not failures:
        for k, (p, ia, ib, desc) in roots.items():
            if realize_fork(wit[ia], wit[ib], desc, k) is None:
                root_fail.append({'from': [ia, ib], 'desc': repr(desc)})
    sizes = [w[0].nv for w in wit if w is not None]
    print(json.dumps({
        'w': args.w, 'closure_states': len(states), 'closure_roots': len(roots),
        'realized_states': sum(1 for x in wit if x is not None),
        'failures': failures, 'root_failures': root_fail,
        'max_piece_vertices': max(sizes), 'closure_seconds': round(t1 - t0, 1),
        'realize_seconds': round(time.time() - t1, 1)}))
    return 0


if __name__ == '__main__':
    sys.exit(main())
