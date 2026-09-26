"""Generate test pieces for piece_support.

Piece format: "n m k", m internal edges, k port vertices in cyclic boundary
order, k port signs (+1/-1, bipartition class of the port vertex when the
piece's internal graph is bipartite, else +1).
"""
import math
import os
import sys

import networkx as nx


def write_piece(path, n, edges, ports, signs=None):
    if signs is None:
        signs = [1] * len(ports)
    with open(path, "w") as f:
        f.write(f"{n} {len(edges)} {len(ports)}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")
        f.write(" ".join(map(str, ports)) + "\n")
        f.write(" ".join(map(str, signs)) + "\n")


def cycle_cap(k):
    edges = [(i, (i + 1) % k) for i in range(k)]
    return k, edges, list(range(k))


def cap_rings(k, rings):
    """k-cycle, spokes, then `rings` zigzag rings; ports on the last ring."""
    edges = [(i, (i + 1) % k) for i in range(k)]
    n = k
    prev = list(range(k))  # vertices carrying the outgoing half-edges
    for _ in range(rings):
        ins = list(range(n, n + k)); n += k
        outs = list(range(n, n + k)); n += k
        for i in range(k):
            edges.append((prev[i], ins[i]))
        for i in range(k):
            edges.append((ins[i], outs[i]))
            edges.append((ins[(i + 1) % k], outs[i]))
        prev = outs
    return n, edges, prev


def hex_disc(cells):
    """Benzenoid from axial hexagon coordinates; ports at degree-2 vertices."""
    key = lambda x, y: (round(x, 5), round(y, 5))
    vid, pos, edges, cls = {}, [], set(), {}
    for (q, r) in cells:
        cx, cy = math.sqrt(3) * (q + r / 2), 1.5 * r
        corners = []
        for t in range(6):
            ang = math.radians(30 + 60 * t)
            p = key(cx + math.cos(ang), cy + math.sin(ang))
            if p not in vid:
                vid[p] = len(pos); pos.append(p); cls[vid[p]] = t % 2
            corners.append(vid[p])
        for t in range(6):
            a, b = corners[t], corners[(t + 1) % 6]
            edges.add((min(a, b), max(a, b)))
    g = nx.Graph(); g.add_edges_from(edges)
    n = len(pos)
    # boundary: edges on exactly one hexagon
    count = {}
    for (q, r) in cells:
        cx, cy = math.sqrt(3) * (q + r / 2), 1.5 * r
        cs = [vid[key(cx + math.cos(math.radians(30 + 60 * t)), cy + math.sin(math.radians(30 + 60 * t)))] for t in range(6)]
        for t in range(6):
            e = (min(cs[t], cs[(t + 1) % 6]), max(cs[t], cs[(t + 1) % 6]))
            count[e] = count.get(e, 0) + 1
    bnd = [e for e, c in count.items() if c == 1]
    bg = nx.Graph(); bg.add_edges_from(bnd)
    cycle = [u for u, v in nx.find_cycle(bg)]
    # orient counterclockwise by signed area
    area = sum(pos[cycle[i]][0] * pos[cycle[(i + 1) % len(cycle)]][1] - pos[cycle[(i + 1) % len(cycle)]][0] * pos[cycle[i]][1] for i in range(len(cycle)))
    if area < 0:
        cycle.reverse()
    ports = [v for v in cycle if g.degree(v) == 2]
    signs = [1 if cls[v] == 0 else -1 for v in ports]
    return n, sorted(edges), ports, signs


def corannulene():
    # hub pentagon 0..4, spokes to 5..9, rim 10..19
    edges = [(i, (i + 1) % 5) for i in range(5)]
    for i in range(5):
        edges.append((i, 5 + i))
    for i in range(5):
        a, b = 10 + 2 * i, 11 + 2 * i
        edges.append((5 + i, a))
        edges.append((a, b))
        edges.append((b, 5 + (i + 1) % 5))
    ports = list(range(10, 20))
    return 20, edges, ports


def main(out):
    os.makedirs(out, exist_ok=True)
    for k in (5, 6, 7):
        write_piece(f"{out}/cycle{k}.txt", *cycle_cap(k))
        for r in (1, 2):
            write_piece(f"{out}/cap{k}_r{r}.txt", *cap_rings(k, r))
    discs = {
        "naphthalene": [(0, 0), (1, 0)],
        "anthracene": [(0, 0), (1, 0), (2, 0)],
        "phenanthrene": [(0, 0), (1, 0), (1, 1)],
        "pyrene": [(0, 0), (1, 0), (0, 1), (1, -1)],
                "perylene": [(0, 0), (1, 0), (0, 1), (2, -1), (1, -1)],
        "coronene": [(0, 0), (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)],
        "tetracene": [(0, 0), (1, 0), (2, 0), (3, 0)],
    }
    for name, cells in discs.items():
        write_piece(f"{out}/{name}.txt", *hex_disc(cells))
    circum = [(q, r) for q in range(-2, 3) for r in range(-2, 3) if abs(q + r) <= 2]
    write_piece(f"{out}/circumcoronene.txt", *hex_disc(circum))
    write_piece(f"{out}/corannulene.txt", *corannulene())


if __name__ == "__main__":
    main(sys.argv[1])
