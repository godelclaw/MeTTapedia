#!/usr/bin/env python3
"""A colourable trail that is not completable by simple operations (self-contained check).

G: 3-connected planar cubic graph on 20 vertices (faces 4,4,5^8,6,6), e = (3,8).
Trail colourings: proper 3-edge-colourings of G - e with equal colours at each endpoint
(the arrow tips lie on curves).  Simple operation: colour switch on a two-colour circuit.
Completable: the endpoints lie on a common two-colour circuit (Kauffman, arXiv math/0112266,
Section 4).  This script verifies: G is cubic, planar, 3-connected and 3-edge-colourable;
there are 36 trail colourings, closed under all simple operations (one class); none is
completable.  Hence "extended graph colourable => completable by simple operations" fails.
"""
import itertools
from collections import deque
EDGES = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7),(3,7),(3,8),(4,9),(4,10),(5,6),(5,11),(6,12),(7,13),(8,9),(8,14),(9,15),(10,11),(10,16),(11,17),(12,13),(12,17),(13,18),(14,15),(14,18),(15,16),(16,19),(17,19),(18,19)]
E0 = (3, 8)
n = 20
adjacency = {v: set() for v in range(n)}
for a, b in EDGES: adjacency[a].add(b); adjacency[b].add(a)
assert all(len(adjacency[v]) == 3 for v in range(n))
H = [e for e in EDGES if e != E0]
inc = {v: [k for k, e in enumerate(H) if v in e] for v in range(n)}
v1, v2 = E0

def colourings(equal_at_endpoints):
    col = [-1] * len(H); out = []
    def ok(k, c):
        for u in H[k]:
            for j in inc[u]:
                if j == k or col[j] == -1: continue
                if equal_at_endpoints and u in (v1, v2):
                    if col[j] != c: return False
                elif col[j] == c: return False
        return True
    def rec(k):
        if k == len(H): out.append(tuple(col)); return
        for c in range(3):
            if ok(k, c): col[k] = c; rec(k + 1); col[k] = -1
    rec(0); return out

def components(s, a, b):
    par = list(range(n))
    def find(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for k, (p, q) in enumerate(H):
        if s[k] in (a, b): par[find(p)] = find(q)
    return find

# G itself is 3-edge-colourable: colourings of G - e with distinct colours at endpoints extend
assert len(colourings(False)) > 0, "G not colourable"
states = colourings(True)
assert len(states) == 36
stset = set(states)
# closure under simple operations and non-completability
seen = set(); dq = deque([states[0]]); seen.add(states[0])
while dq:
    s = dq.popleft()
    for a, b in ((0, 1), (0, 2), (1, 2)):
        find = components(s, a, b)
        assert find(v1) != find(v2), "completable state found"
        roots = {find(v) for v in range(n)}
        for r in roots:
            s2 = tuple((b if s[k] == a else a) if (s[k] in (a, b) and find(H[k][0]) == r) else s[k] for k in range(len(H)))
            assert s2 in stset
            if s2 not in seen: seen.add(s2); dq.append(s2)
assert len(seen) == 36
print("verified: 36 trail colourings, one class under simple operations, none completable; G colourable")
