"""Closure-free (zero-Kempe) cap reducibility for large disks.

A disk K with n ports is reducible by the cap mu (a noncrossing pairing of
the ports, 0 vertices) if supp(cap) is contained in supp(K), i.e. every
assignment of colours to the pairs extends to a proper colouring of K.
No Kempe closure is needed, so this scales to rings far beyond 3^n word
tables: each word is one constraint-satisfaction extension test.

Method: for each cap, test a fixed pseudo-random sample of pair-colourings
first (early reject on the first non-extendable word); caps that survive
the sample are verified on all 3^(n/2) words, modulo colour permutation
(only words with first pair colour 0 and first differing colour 1 are
tested; colour permutations are symmetries of both cap and K).

Pre-registered: ZK1 = some cap survives full verification -> the disk is
reducible with a certificate needing no Kempe rounds; ZK2 = every cap is
rejected -> zero-Kempe cap reduction fails for this disk (Kempe closure or
larger replacements needed).

Usage: python3 cap_zero_kempe_test.py tangle.json [sample] [max_caps]
"""
import sys, json, time, random, itertools
sys.path.insert(0, '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp')
from kempe import noncrossing


def load(path):
    d = json.load(open(path))
    E = [tuple(tuple(z) if isinstance(z, list) else z for z in e) for e in d['edges']]
    E = [(('p', z[1]) if isinstance(z, tuple) else z for z in e) for e in E]
    E = [tuple(e) for e in E]
    return d['n'], d['nv'], E


class Extender:
    """Backtracking extension test: does K admit a proper colouring with the
    given port colours?  Edges ordered by BFS from the ports; vertex
    constraint checked incrementally."""
    def __init__(self, n, nv, E):
        self.n, self.nv = n, nv
        self.E = E
        self.m = len(E)
        inc = [[] for _ in range(nv)]
        self.port_edge = [None] * n
        for k, (u, v) in enumerate(E):
            for z in (u, v):
                if isinstance(z, tuple): self.port_edge[z[1]] = k
                else: inc[z].append(k)
        self.inc = inc
        self.edge_verts = [[z for z in e if not isinstance(z, tuple)] for e in E]
        # order: port edges first (fixed), then BFS
        order = [self.port_edge[i] for i in range(n)]
        seen = set(order); frontier = list(order)
        while frontier:
            nxt = []
            for k in frontier:
                for v in self.edge_verts[k]:
                    for e in inc[v]:
                        if e not in seen:
                            seen.add(e); order.append(e); nxt.append(e)
            frontier = nxt
        for k in range(self.m):
            if k not in seen: order.append(k)
        self.order = order
        sys.setrecursionlimit(10000)

    def extends(self, word):
        col = [-1] * self.m
        for i, c in enumerate(word):
            col[self.port_edge[i]] = c
        # quick vertex check for port edges sharing a vertex
        inc, ev, order = self.inc, self.edge_verts, self.order
        def ok_at(k, c):
            for v in ev[k]:
                for e in inc[v]:
                    if e != k and col[e] == c: return False
            return True
        for i in range(self.n):
            k = self.port_edge[i]
            if not ok_at(k, col[k]): return False
        def rec(idx):
            if idx == len(order): return True
            k = order[idx]
            if col[k] >= 0:
                return rec(idx + 1)
            for c in (0, 1, 2):
                if ok_at(k, c):
                    col[k] = c
                    if rec(idx + 1): return True
                    col[k] = -1
            return False
        return rec(self.n)


def cap_words(pairs, canonical_only=True):
    """all colourings of the pairs; with canonical_only, fix the first pair to 0
    and the first other colour to 1 (colour-permutation representatives)."""
    m = len(pairs)
    for cols in itertools.product((0, 1, 2), repeat=m):
        if canonical_only:
            if cols[0] != 0: continue
            rest = [c for c in cols if c != 0]
            if rest and rest[0] != 1: continue
        yield cols


def word_of(pairs, cols, n):
    w = [None] * n
    for (i, j), c in zip(pairs, cols):
        w[i] = c; w[j] = c
    return w


def main():
    path = sys.argv[1]
    sample = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    max_caps = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
    n, nv, E = load(path)
    X = Extender(n, nv, E)
    caps = noncrossing(list(range(n)))
    print(f"{path}: ring {n}, vertices {nv}, caps {len(caps)}", flush=True)
    rng = random.Random(12345)
    m = n // 2
    survivors = []; t0 = time.time(); rejected_at = []
    for ci, mu in enumerate(caps[:max_caps]):
        # sample
        bad = False
        for s in range(sample):
            cols = [0] + [rng.randrange(3) for _ in range(m - 1)]
            if not X.extends(word_of(mu, cols, n)):
                bad = True; rejected_at.append(s); break
        if bad: continue
        # full verification (canonical words)
        allok = True; tested = 0
        for cols in cap_words(mu):
            tested += 1
            if not X.extends(word_of(mu, cols, n)):
                allok = False; rejected_at.append(sample + tested); break
        if allok:
            survivors.append(mu)
            print(f"  SURVIVOR cap {mu} (all {tested} canonical words extend)", flush=True)
        if ci % 2000 == 0 and ci:
            print(f"  ... {ci} caps, {len(survivors)} survivors, {time.time()-t0:.0f}s", flush=True)
    print(f"caps tested {min(len(caps), max_caps)}, survivors {len(survivors)}, mean rejection index {sum(rejected_at)/max(1,len(rejected_at)):.1f}, {time.time()-t0:.0f}s")
    print("OUTCOME:", f"ZK1 zero-Kempe cap reduction: {survivors[0]}" if survivors else "ZK2 (no cap survives)")
    json.dump(dict(tangle=path, ring=n, vertices=nv, caps=len(caps), survivors=survivors), open(path.replace('.json', '_capzk.json'), 'w'))


if __name__ == '__main__':
    main()
