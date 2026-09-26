"""Cut a closed cubic map along a vertex set and compare the two supports.

For a vertex set X, side A is G[X] and side B is G[V \\ X]; the ports of both
sides are the cut edges in one fixed order, so a boundary word means the same
thing on both sides.  Supports are colour-permutation invariant, so the sides
are compatible iff some canonical representative lies in both supports.
Reports |cut|, both densities, their sum, and the number of shared
representatives (weighted by orbit size).
"""
import subprocess
import sys
import tempfile
import os
from collections import deque

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(HERE, "piece_support")


def side_piece(G, X, cut):
    X = list(X)
    idx = {v: i for i, v in enumerate(X)}
    edges = [(idx[u], idx[v]) for u, v in G.edges() if u in idx and v in idx]
    ports = [idx[u] if u in idx else idx[v] for u, v in cut]
    return len(X), edges, ports


def support_reps(n, edges, ports):
    with tempfile.NamedTemporaryFile("w", delete=False, suffix=".txt") as f:
        f.write(f"{n} {len(edges)} {len(ports)}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")
        f.write(" ".join(map(str, ports)) + "\n")
        path = f.name
    dump = path + ".dump"
    out = subprocess.run([TOOL, "--dump", dump], stdin=open(path), capture_output=True, text=True).stdout
    first = out.splitlines()[0]
    fields = dict(kv.split("=") for kv in first.split() if "=" in kv)
    reps = set(open(dump).read().split())
    os.unlink(path); os.unlink(dump)
    return int(fields["admissible"]), int(fields["support"]), reps


def orbit_size(rep):
    return 3 if len(set(rep)) == 1 else 6


def compare(G, X, label):
    X = set(X)
    Y = set(G.nodes()) - X
    cut = [(u, v) for u, v in G.edges() if (u in X) != (v in X)]
    if not (nx.is_connected(G.subgraph(X)) and nx.is_connected(G.subgraph(Y))):
        print(f"{label}: sides not connected, skipped"); return
    nA, eA, pA = side_piece(G, X, cut)
    nB, eB, pB = side_piece(G, Y, cut)
    adm, sA, rA = support_reps(nA, eA, pA)
    _, sB, rB = support_reps(nB, eB, pB)
    shared = sum(orbit_size(r) for r in rA & rB)
    print(f"{label}: |X|={len(X)} |Y|={len(Y)} cut={len(cut)} admissible={adm} "
          f"dA={sA/adm:.3f} dB={sB/adm:.3f} sum={(sA+sB)/adm:.3f} shared={shared}"
          f"{'  pigeonhole certifies' if sA + sB > adm else ''}")
    sys.stdout.flush()


def truncate(T):
    """Truncation of a triangulation with a planar embedding: a cubic map."""
    ok, emb = nx.check_planarity(T)
    assert ok
    G = nx.Graph()
    for v in T.nodes():
        nbrs = list(emb.neighbors_cw_order(v))
        for i, u in enumerate(nbrs):
            w = nbrs[(i + 1) % len(nbrs)]
            G.add_edge((v, u), (v, w))
            G.add_edge((v, u), (u, v))
    return G


def ball(G, seeds, r):
    dist = {s: 0 for s in seeds}
    q = deque(seeds)
    while q:
        v = q.popleft()
        if dist[v] == r:
            continue
        for u in G.neighbors(v):
            if u not in dist:
                dist[u] = dist[v] + 1
                q.append(u)
    return set(dist)


def main():
    maps = {}
    maps["C20"] = nx.dodecahedral_graph()
    maps["C60"] = nx.convert_node_labels_to_integers(truncate(nx.icosahedral_graph()))
    for name, G in maps.items():
        assert all(d == 3 for _, d in G.degree()), name
        cyc = nx.minimum_cycle_basis(G)
        pent = [c for c in cyc if len(c) == 5]
        hexa = [c for c in cyc if len(c) == 6]
        seeds = [("pentagon", pent[0])] + ([("hexagon", hexa[0])] if hexa else [])
        for sname, face in seeds:
            for r in range(0, 6):
                X = ball(G, face, r)
                if len(X) >= len(G) - 5:
                    break
                cut = sum(1 for u, v in G.edges() if (u in X) != (v in X))
                if cut > 14:
                    continue
                compare(G, X, f"{name} {sname}-ball r={r}")


if __name__ == "__main__":
    main()
