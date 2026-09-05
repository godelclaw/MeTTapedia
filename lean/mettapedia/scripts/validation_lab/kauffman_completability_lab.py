#!/usr/bin/env python3
"""Kauffman's completability, tested on small planar cubic graphs.

Kauffman (arXiv math/0112266, Section 4): a trail is a formation with two blue container
curves and an empty edge between them; it is *completable over the empty edge* when the
two arrow tips are joined by a two-colour pathway (the complex operation then switches
along the pathway and colours the empty edge); it is *completable by simple operations*
when closed-circuit Kempe switches can transform the formation into a completable one.
The manuscript's (v23, Section 3) rendering "the two missing colours at the endpoints
agree" is automatic by parity and is not this condition.

Graph model: G planar cubic bridgeless (hence 3-edge-colourable by 4CT), e = v1 v2; states
are proper colourings of G - e in which each endpoint's two edges carry EQUAL colours (the
endpoint sits on a curve; closed-circuit switches preserve this); a state is completable if
v1 and v2 lie on a common two-colour circuit (then the path-switch plus the new edge gives
a proper colouring of G).  Test: every closed-circuit Kempe class of such states contains
a completable state.  Pre-registered outcomes: P1 = no violating class (the hypothesis of
the reduction survives at graph level); P2 = a violating class (a trail whose extended
graph is colourable but which is not completable by simple operations: the reduction's
hypothesis is false as a universal statement).

Usage: kauffman_completability_lab.py NMAX [samples-per-n]
"""
import sys, random, json
from collections import deque
import networkx as nx

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
SAMPLES = int(sys.argv[2]) if len(sys.argv) > 2 else 400
random.seed(11)


def random_cubic(n):
    half = [v for v in range(n) for _ in range(3)]
    for _ in range(60):
        random.shuffle(half)
        edges = [(half[i], half[i + 1]) for i in range(0, len(half), 2)]
        if any(a == b for a, b in edges): continue
        es = set(frozenset(e) for e in edges)
        if len(es) < len(edges): continue
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(tuple(e) for e in es)
        if nx.is_connected(G) and nx.check_planarity(G)[0] and nx.is_k_edge_connected(G, 2):
            return G
    return None


def states(H, v1, v2):
    """proper colourings of H = G - e, with equal colours at v1 and at v2"""
    edges = list(H.edges())
    idx = {frozenset(e): i for i, e in enumerate(edges)}
    inc = {v: [idx[frozenset(e)] for e in H.edges(v)] for v in H.nodes()}
    col = [-1] * len(edges); out = []

    def ok(k, c):
        a, b = edges[k]
        for v in (a, b):
            if v in (v1, v2):
                for j in inc[v]:
                    if j != k and col[j] != -1 and col[j] != c: return False
            else:
                for j in inc[v]:
                    if j != k and col[j] == c: return False
        return True

    def rec(k):
        if k == len(edges): out.append(tuple(col)); return
        for c in range(3):
            if ok(k, c): col[k] = c; rec(k + 1); col[k] = -1
    rec(0)
    return edges, inc, out


def components(edges, c, a, b):
    """two-colour components as (vertex set, closed?)"""
    sub = [k for k in range(len(edges)) if c[k] in (a, b)]
    adj = {}
    for k in sub:
        for v in edges[k]: adj.setdefault(v, []).append(k)
    done = set(); comps = []
    for k in sub:
        if k in done: continue
        compE = []; st = [k]; done.add(k)
        while st:
            x = st.pop(); compE.append(x)
            for v in edges[x]:
                for y in adj[v]:
                    if y not in done: done.add(y); st.append(y)
        degs = {}
        for x in compE:
            for v in edges[x]: degs[v] = degs.get(v, 0) + 1
        comps.append((compE, set(degs), all(d == 2 for d in degs.values())))
    return comps


def completable(edges, c, v1, v2):
    for a, b in ((0, 1), (0, 2), (1, 2)):
        for compE, verts, closed in components(edges, c, a, b):
            if v1 in verts and v2 in verts: return True
    return False


def kempe_class_check(edges, inc, sts, v1, v2):
    stset = set(sts); seen = set(); classes = []
    for s0 in sts:
        if s0 in seen: continue
        cls = []; dq = deque([s0]); seen.add(s0)
        while dq:
            c = dq.popleft(); cls.append(c)
            for a, b in ((0, 1), (0, 2), (1, 2)):
                for compE, verts, closed in components(edges, c, a, b):
                    if not closed: continue
                    c2 = list(c)
                    for x in compE: c2[x] = b if c[x] == a else a
                    c2 = tuple(c2)
                    if c2 in stset and c2 not in seen: seen.add(c2); dq.append(c2)
        classes.append(cls)
    return classes


results = {"per_n": {}, "violations": []}
for n in range(4, NMAX + 1, 2):
    graphs = []
    for _ in range(SAMPLES):
        G = random_cubic(n)
        if G is None: continue
        if any(nx.is_isomorphic(G, K) for K in graphs): continue
        graphs.append(G)
    trails = classes_n = bad = 0
    for G in graphs:
        for e in list(G.edges()):
            v1, v2 = e
            H = G.copy(); H.remove_edge(v1, v2)
            edges, inc, sts = states(H, v1, v2)
            if not sts: continue
            trails += 1
            for cls in kempe_class_check(edges, inc, sts, v1, v2):
                classes_n += 1
                if not any(completable(edges, c, v1, v2) for c in cls):
                    bad += 1
                    results["violations"].append({"n": n, "edges": [list(x) for x in G.edges()], "e": [v1, v2],
                                                  "class_size": len(cls), "state": list(cls[0])})
    results["per_n"][n] = {"graphs": len(graphs), "trails": trails, "classes": classes_n, "violating": bad}
    print(f"n={n}: graphs {len(graphs)} trails {trails} classes {classes_n} violating {bad}", flush=True)
json.dump(results, open("kauffman_completability_results.json", "w"), indent=1)
print("DONE violations:", len(results["violations"]))
