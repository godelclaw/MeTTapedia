#!/usr/bin/env python3
"""Tait-type orbit along a (k,0) zigzag tube.

The inner part after r rings is a k-gon cap plus r zigzag rings; the cut after
ring r crosses exactly k edges.  Its Tait type is the set of parity-legal
boundary words (colourings of the k crossed edges) that extend to a Tait
colouring of the inner part.  Two nested cuts with equal Tait type make the
slab between them deletable in a vertex-minimal counterexample, so the first
repeat along the tube is the corridor length the pumping argument needs.

Usage: tube_tait_type_orbit_lab.py [k] [max_rings]
"""
import sys, itertools


def tube(k, r):
    """Vertices: cap c_i (0..k-1); ring t (1..r): d^t_i = k + 2k(t-1) + i, e^t_i = d^t_i + k.
    Returns (nv, edges, ports) where ports are the k edges crossing the cut after ring r,
    listed as (edge index, ring position i)."""
    edges = []
    def add(u, v):
        edges.append((u, v)); return len(edges) - 1
    for i in range(k):
        add(i, (i + 1) % k)
    d = lambda t, i: k + 2 * k * (t - 1) + i
    e = lambda t, i: d(t, i) + k
    for t in range(1, r + 1):
        for i in range(k):
            add(d(t, i), e(t, i)); add(e(t, i), d(t, (i + 1) % k))
            if t == 1:
                add(i, d(t, i))
            else:
                add(e(t - 1, i), d(t, i))
    nv = k + 2 * k * r
    # ports: dangling edges to a virtual outside vertex (-1 - i)
    ports = []
    for i in range(k):
        src = i if r == 0 else e(r, i)
        ports.append((add(src, -1 - i), i))
    return nv, edges, ports


def legal_words(k):
    out = []
    for w in itertools.product(range(3), repeat=k):
        cnt = [w.count(c) for c in range(3)]
        if len({c % 2 for c in cnt}) == 1:
            out.append(w)
    return out


def tait_type(k, r):
    nv, E, ports = tube(k, r)
    adj = {v: [] for v in range(nv)}
    for ei, (u, v) in enumerate(E):
        if u >= 0: adj[u].append(ei)
        if v >= 0: adj[v].append(ei)
    order = list(range(nv))  # cap first, then rings in order: a good DFS order
    port_edge = {i: ei for ei, i in ports}

    def extends(word):
        col = {port_edge[i]: c for i, c in enumerate(word)}
        def ok(v):
            cs = [col[x] for x in adj[v] if x in col]
            return len(cs) == len(set(cs))
        def rec(idx):
            if idx == nv: return True
            v = order[idx]
            free = [x for x in adj[v] if x not in col]
            used = {col[x] for x in adj[v] if x in col}
            avail = [c for c in range(3) if c not in used]
            if len(avail) < len(free): return False
            for perm in itertools.permutations(avail, len(free)):
                for x, c in zip(free, perm): col[x] = c
                good = all(ok(z) for x in free for z in E[x] if z >= 0)
                if good and rec(idx + 1): return True
                for x in free: del col[x]
            return False
        return rec(0)

    return frozenset(w for w in legal_words(k) if extends(w))


def main():
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    words = legal_words(k)
    print(f"(k,0) tube k={k}: {len(words)} parity-legal boundary words")
    seen = {}
    for r in range(R + 1):
        T = tait_type(k, r)
        tag = f"r={r:2d} vertices={k + 2 * k * r:3d} |type|={len(T):3d}"
        if T in seen:
            print(f"{tag}  REPEAT of r={seen[T]}  -> orbit closes: preperiod {seen[T]}, period {r - seen[T]}")
            break
        seen[T] = r
        print(tag)
    else:
        print("no repeat within range")


if __name__ == '__main__':
    main()


# ---------- ring relation and universal orbit bound
def ring_relation(k):
    """R[w] = set of out-words reachable from in-word w across ONE zigzag ring
    (d_i in-port, e_i out-port).  Any inner side S gives Ext(S + ring) = R[S]."""
    edges = []
    def add(u, v):
        edges.append((u, v)); return len(edges) - 1
    d = lambda i: i
    e = lambda i: k + i
    inp = [add(-1 - i, d(i)) for i in range(k)]
    for i in range(k):
        add(d(i), e(i)); add(e(i), d((i + 1) % k))
    out = [add(e(i), -100 - i) for i in range(k)]
    nv = 2 * k
    adj = {v: [] for v in range(nv)}
    for ei, (u, v) in enumerate(edges):
        if u >= 0: adj[u].append(ei)
        if v >= 0: adj[v].append(ei)
    words = legal_words(k)
    R = {}
    for w in words:
        col0 = {inp[i]: c for i, c in enumerate(w)}
        outs = set()
        def rec(idx, col):
            if idx == nv:
                outs.add(tuple(col[out[i]] for i in range(k))); return
            v = idx
            free = [x for x in adj[v] if x not in col]
            used = {col[x] for x in adj[v] if x in col}
            avail = [c for c in range(3) if c not in used]
            if len(avail) < len(free): return
            for perm in itertools.permutations(avail, len(free)):
                for x, c in zip(free, perm): col[x] = c
                good = True
                for x in free:
                    for z in edges[x]:
                        if z >= 0:
                            cs = [col[y] for y in adj[z] if y in col]
                            if len(cs) != len(set(cs)): good = False
                if good: rec(idx + 1, col)
                for x in free: del col[x]
        rec(0, dict(col0))
        R[w] = frozenset(outs)
    return words, R


def orbit(R, S):
    seen = {}
    r = 0
    while S not in seen:
        seen[S] = r
        S = frozenset(x for w in S for x in R[w]); r += 1
    return seen[S], r - seen[S]   # preperiod, period


def universal(k):
    words, R = ring_relation(k)
    sym = all(a in R[b] for a in words for b in R[a])
    worst = max((orbit(R, frozenset([w])) for w in words), key=lambda t: t[0] + t[1])
    pre = max(orbit(R, frozenset([w]))[0] for w in words)
    per = max(orbit(R, frozenset([w]))[1] for w in words)
    full = orbit(R, frozenset(words))
    print(f"k={k}: |W|={len(words)} relation symmetric={sym} "
          f"singleton orbits: max preperiod {pre}, max period {per}; from all words: {full}")
    return pre, per


if __name__ == '__main__' and len(sys.argv) > 3 and sys.argv[3] == 'universal':
    for kk in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        universal(kk)
