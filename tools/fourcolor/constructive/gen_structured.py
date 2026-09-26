"""Structured normal-form maps for the pentagon-complement falsifier.

Families (all written as plantri ASCII, one map per line, at most 158 vertices):
  tube k m1 m2   k-gon polar cap + ring of k pentagons + m1 hexagon rings,
                 glued to a mirrored cap with m2 rings (capped (k,0) tubes;
                 k = 5 gives fullerene nanotubes with nontrivial 5-cuts)
  dumbbell f m   two copies of C60 minus a face of length f (5 or 6), joined
                 by a zigzag tube of m rings (thin f-edge necks)
  tadpole f m    C60 minus a face of length f, a tube of m rings, then a cycle
                 cap with its pentagon ring
Each map is checked: cubic, planar with V - E + F = 2, faces of length >= 5,
and no cyclic edge cut of size <= 4 (via dual cycles of length <= 4).
Rejected maps are reported on stderr with the reason.
Usage: python3 gen_structured.py > structured.txt
"""
import sys
import networkx as nx


def c60():
    ico = nx.icosahedral_graph()
    ok, emb = nx.check_planarity(ico)
    G = nx.Graph()
    for v in ico.nodes():
        nb = list(emb.neighbors_cw_order(v))
        for i, u in enumerate(nb):
            G.add_edge((v, u), (v, nb[(i + 1) % len(nb)]))
            G.add_edge((v, u), (u, v))
    return nx.convert_node_labels_to_integers(G)


def faces_of(G):
    ok, emb = nx.check_planarity(G)
    if not ok:
        return None, None
    seen, faces = set(), []
    for u, v in emb.edges():
        if (u, v) in seen:
            continue
        faces.append(emb.traverse_face(u, v, mark_half_edges=seen))
    return emb, faces


def normal_form_reason(G):
    if any(d != 3 for _, d in G.degree()):
        return "not cubic"
    emb, faces = faces_of(G)
    if emb is None:
        return "not planar"
    if G.number_of_nodes() - G.number_of_edges() + len(faces) != 2:
        return "Euler"
    if min(len(f) for f in faces) < 5:
        return "short face"
    shared = {}
    for i, f in enumerate(faces):
        for t in range(len(f)):
            shared.setdefault(frozenset((f[t], f[(t + 1) % len(f)])), []).append(i)
    pair_edges = {}
    for e, fl in shared.items():
        if fl[0] == fl[1]:
            return "bridge"
        pair_edges.setdefault(frozenset(fl), []).append(tuple(e))
    if any(len(v) >= 2 for v in pair_edges.values()):
        return "faces share two edges (2-cut)"
    D = nx.Graph()
    for p in pair_edges:
        a, b = tuple(p)
        D.add_edge(a, b)
    # dual cycles of length 3 and 4 are the candidate cyclic 3- and 4-edge cuts
    for s in D.nodes():
        stack = [(s, [s])]
        while stack:
            v, path = stack.pop()
            for w in D[v]:
                if w == s and len(path) >= 3:
                    cut = [pair_edges[frozenset((path[i], path[(i + 1) % len(path)]))][0]
                           for i in range(len(path))]
                    H = G.copy()
                    H.remove_edges_from(cut)
                    comps = list(nx.connected_components(H))
                    cyclic = sum(1 for c in comps if H.subgraph(c).number_of_edges() >= len(c))
                    if cyclic >= 2:
                        return f"cyclic {len(path)}-cut"
                elif w > s and w not in path and len(path) < 4:
                    stack.append((w, path + [w]))
    return None


def ascii_code(G):
    G = nx.convert_node_labels_to_integers(G)
    emb, faces = faces_of(G)
    n = G.number_of_nodes()
    assert n <= 158
    parts = []
    for v in range(n):
        parts.append(bytes(97 + u for u in emb.neighbors_cw_order(v)))
    return str(n).encode() + b" " + b",".join(parts)


def add_cap(G, tag, k, ports):
    """Attach a k-cycle cap (with its ring of k pentagons) to k ports in order."""
    for i in range(k):
        G.add_edge((tag, "cap", i), (tag, "cap", (i + 1) % k))
        G.add_edge((tag, "cap", i), ports[i])


def add_rings(G, tag, k, ports, m):
    """Attach m zigzag rings to k ports; return the new outward ports."""
    for r in range(m):
        ins = [(tag, r, "in", i) for i in range(k)]
        outs = [(tag, r, "out", i) for i in range(k)]
        for i in range(k):
            G.add_edge(ports[i], ins[i])
            G.add_edge(ins[i], outs[i])
            G.add_edge(ins[(i + 1) % k], outs[i])
        ports = outs
    return ports


def open_face(G, face):
    """Remove a face; return the spoke endpoints in face order."""
    ports = []
    for x in face:
        outside = [y for y in G[x] if y not in face]
        assert len(outside) == 1
        ports.append(outside[0])
    G.remove_nodes_from(face)
    return ports


def tube(k, m1, m2):
    G = nx.Graph()
    cyc = [("c1", i) for i in range(k)]
    for i in range(k):
        G.add_edge(cyc[i], cyc[(i + 1) % k])
    # spokes from the first cap into its pentagon ring, then m1 + m2 rings, then second cap
    ports = add_rings(G, "t", k, cyc, 1 + m1 + m2)
    add_cap(G, "c2", k, ports[::-1])
    return G


def c60_face(G, length):
    return next(f for f in faces_of(G)[1] if len(f) == length)


def dumbbell(f, m):
    G = nx.Graph()
    A = nx.relabel_nodes(c60(), lambda v: ("A", v))
    B = nx.relabel_nodes(c60(), lambda v: ("B", v))
    pa = open_face(A, c60_face(A, f))
    pb = open_face(B, c60_face(B, f))
    G.add_edges_from(A.edges()); G.add_edges_from(B.edges())
    ports = add_rings(G, "n", f, pa, m) if m > 0 else pa
    for i in range(f):
        G.add_edge(ports[i], pb[(-i) % f])
    return G


def tadpole(f, m):
    G = nx.Graph()
    A = nx.relabel_nodes(c60(), lambda v: ("A", v))
    pa = open_face(A, c60_face(A, f))
    G.add_edges_from(A.edges())
    ports = add_rings(G, "n", f, pa, m + 1)
    add_cap(G, "cap", f, ports[::-1])
    return G


def emit(label, G):
    reason = normal_form_reason(G)
    if reason is not None:
        # try the mirrored identification once (orientation mismatch shows up as non-planarity)
        sys.stderr.write(f"rejected {label}: {reason}\n")
        return
    sys.stdout.buffer.write(ascii_code(G) + b"\n")
    sys.stderr.write(f"ok {label} V={G.number_of_nodes()}\n")


def main():
    for k in range(5, 11):
        for m in range(0, 12):
            G = tube(k, m, m)
            if G.number_of_nodes() > 158:
                break
            emit(f"tube k={k} m={m}+{m}", G)
    for f in (5, 6):
        for m in range(0, 5):
            G = dumbbell(f, m)
            if G.number_of_nodes() > 158:
                break
            emit(f"dumbbell f={f} m={m}", G)
    for f in (5, 6):
        for m in range(0, 8):
            G = tadpole(f, m)
            if G.number_of_nodes() > 158:
                break
            emit(f"tadpole f={f} m={m}", G)


if __name__ == "__main__":
    main()
