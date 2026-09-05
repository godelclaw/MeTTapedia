#!/usr/bin/env python3
"""Local reachability equivalence (Goertzel v23 Theorem 3.1 hypothesis), tested.

For every trail: (extended graph 3-edge-colourable) <=> (completable by between-region
Kempe switches), where completable means: from the given colouring of G - e, some finite
sequence of Kempe switches, each on a closed two-colour circuit, reaches a colouring in
which the two missing colours at the endpoints of e agree.  The nontrivial direction is
=>: for a colourable planar cubic G and any edge e, every Kempe class of colourings of
G - e (switches on closed two-colour circuits of G - e) must contain an extendable one.

This lab samples planar cubic graphs on n <= NMAX vertices (random matchings, planarity
test, isomorphism dedup), and for each edge e checks every Kempe class of G - e.

Finding (2026-09-05): with distinct colours required at the two degree-2 endpoints (the
paper's stated convention), the two missing colours agree in EVERY colouring of G - e, by
counting: each colour class is a matching covering all vertices except the endpoints that
miss it, and the vertex count is even.  So completability is automatic and the hypothesis
of Theorem 3.1 is vacuous at graph level (0 mismatches in 7,992 colourings over 208
graphs).  Under the formation's own convention (a marked point on a container curve has
both edges of the container's colour) no closed-circuit switch can separate them, so
nothing is completable.  The content of the reduction must live in Kauffman's formation
calculus, which the paper sets aside.

Pre-registered outcomes: P1 = every class extendable on all graphs tested (hypothesis
survives); P2 = a class with no extendable colouring (a trail violating the hypothesis:
Theorem 3.1's premise is false and the route needs a weaker reduction).

Usage: kauffman_reachability_lab.py NMAX [samples-per-n]
"""
import sys, random, itertools, json
from collections import deque
try:
    import networkx as nx
except ImportError:
    print("networkx required"); sys.exit(2)

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10
SAMPLES = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
random.seed(4)


def random_cubic(n):
    half = [v for v in range(n) for _ in range(3)]
    for _ in range(50):
        random.shuffle(half)
        edges = [(half[i], half[i + 1]) for i in range(0, len(half), 2)]
        if any(a == b for a, b in edges): continue
        es = set(frozenset(e) for e in edges)
        if len(es) < len(edges): continue
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(tuple(e) for e in es)
        if nx.is_connected(G) and nx.check_planarity(G)[0]:
            return G
    return None


def colourings(G, deg2):
    """all proper 3-edge-colourings of G (dict edge->colour), backtracking"""
    edges = list(G.edges())
    idx = {frozenset(e): i for i, e in enumerate(edges)}
    inc = {v: [idx[frozenset(e)] for e in G.edges(v)] for v in G.nodes()}
    col = [-1] * len(edges)
    out = []

    def ok(k, c):
        a, b = edges[k]
        for v in (a, b):
            for j in inc[v]:
                if j != k and col[j] == c: return False
        return True

    def rec(k):
        if k == len(edges):
            out.append(tuple(col)); return
        for c in range(3):
            if ok(k, c):
                col[k] = c; rec(k + 1); col[k] = -1
    rec(0)
    return edges, inc, out


def kempe_classes(edges, inc, cols, nodes):
    """classes under switches on CLOSED two-colour circuits"""
    colset = set(cols)
    seen = set()
    classes = []
    for c0 in cols:
        if c0 in seen: continue
        comp = []
        dq = deque([c0]); seen.add(c0)
        while dq:
            c = dq.popleft(); comp.append(c)
            for a, b in ((0, 1), (0, 2), (1, 2)):
                # components of the (a,b) subgraph
                sub = [k for k in range(len(edges)) if c[k] in (a, b)]
                adj = {}
                for k in sub:
                    for v in edges[k]:
                        adj.setdefault(v, []).append(k)
                done = set()
                for k in sub:
                    if k in done: continue
                    # BFS over edges of the component
                    compE = []; st = [k]; done.add(k)
                    while st:
                        x = st.pop(); compE.append(x)
                        for v in edges[x]:
                            for y in adj[v]:
                                if y not in done: done.add(y); st.append(y)
                    # closed circuit iff every vertex of the component has degree 2 in it
                    degs = {}
                    for x in compE:
                        for v in edges[x]: degs[v] = degs.get(v, 0) + 1
                    if any(d != 2 for d in degs.values()): continue
                    c2 = list(c)
                    for x in compE: c2[x] = b if c[x] == a else a
                    c2 = tuple(c2)
                    if c2 in colset and c2 not in seen:
                        seen.add(c2); dq.append(c2)
        classes.append(comp)
    return classes


def missing_colour(inc, c, v):
    used = {c[k] for k in inc[v]}
    return ({0, 1, 2} - used).pop()


results = {"per_n": {}, "violations": []}
for n in range(4, NMAX + 1, 2):
    seen_hash = set(); graphs = []
    for _ in range(SAMPLES):
        G = random_cubic(n)
        if G is None: continue
        if any(nx.is_isomorphic(G, K) for K in graphs): continue
        graphs.append(G)
    n_trails = 0; n_classes = 0; bad = 0
    for G in graphs:
        if not nx.is_k_edge_connected(G, 2): continue  # bridgeless only
        for e in list(G.edges()):
            H = G.copy(); H.remove_edge(*e)
            edges, inc, cols = colourings(H, e)
            if not cols: continue
            classes = kempe_classes(edges, inc, cols, list(H.nodes()))
            n_trails += 1; n_classes += len(classes)
            for cl in classes:
                if not any(missing_colour(inc, c, e[0]) == missing_colour(inc, c, e[1]) for c in cl):
                    bad += 1
                    results["violations"].append({"n": n, "edges": [list(x) for x in G.edges()], "e": list(e),
                                                  "class_size": len(cl), "example": list(cl[0])})
    results["per_n"][n] = {"graphs": len(graphs), "trails": n_trails, "classes": n_classes, "violating_classes": bad}
    print(f"n={n}: graphs {len(graphs)} trails {n_trails} kempe classes {n_classes} violating {bad}", flush=True)
json.dump(results, open("kauffman_reachability_results.json", "w"), indent=1)
print("DONE; violations:", len(results["violations"]))
