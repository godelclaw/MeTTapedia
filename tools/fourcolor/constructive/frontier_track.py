"""Track the parity invariant along a vertex sweep of a pentagon complement.

For a map G and a pentagonal face P, the complement Y = G - P is processed one
vertex at a time, farthest from P first (ties by vertex number).  The frontier
is the list of edges from processed to unprocessed vertices; at the end it is
the pentagon's five spokes.  The frontier support F is the set of frontier
words (colours 1, 2, 3; xor is the third colour) that extend to a proper
3-edge-colouring of the processed part.  The invariant of the width-change
rule is I_w: all admissible words for odd w, all nonconstant admissible words
for even w.  Each step is classified by how the new vertex meets the frontier:
split (1 old edge), merge (2 old), close (3 old) or start (0 old).

Modes:
  c60                     profile of one pentagon complement of C60: per step
                          the operation, width, density |F| / |A_w| and '*'
                          where F contains I_w
  witnesses [FILE]        summaries for the exceptional pentagons
                          (default exceptional_pentagons.json next to this file)
  stats                   plantri ASCII maps on stdin, first pentagon of each:
                          width at which F first contains I_w mid-sweep
                          (width >= 6, after step 3), later lapses, and final
                          densities below 1

Usage: python3 frontier_track.py c60 | witnesses [FILE] | stats < maps.txt
"""
import json
import os
import sys
from collections import Counter, deque

import networkx as nx


def admissible_count(w):
    return (3 ** w + 3 * (-1) ** w) // 4


def invariant_size(w):
    return admissible_count(w) - (3 if w % 2 == 0 else 0)


def sweep(G, P):
    P = set(P)
    dist = {v: 0 for v in P}
    q = deque(sorted(P))
    while q:
        v = q.popleft()
        for u in G[v]:
            if u not in dist:
                dist[u] = dist[v] + 1
                q.append(u)
    order = sorted((v for v in G if v not in P), key=lambda v: (-dist[v], v))
    processed, frontier, F, steps = set(), [], {()}, []
    for v in order:
        old_pos = [i for i, (a, b) in enumerate(frontier) if b == v]
        new_edges = [(v, u) for u in sorted(G[v]) if u not in processed]
        keep = [i for i in range(len(frontier)) if i not in old_pos]
        newF = set()
        for word in F:
            old_cols = [word[i] for i in old_pos]
            if len(set(old_cols)) < len(old_cols):
                continue
            free = [c for c in (1, 2, 3) if c not in old_cols]
            base = tuple(word[i] for i in keep)
            if not new_edges:
                newF.add(base)
            elif len(new_edges) == 1:
                newF.add(base + (free[0],))
            elif len(new_edges) == 2:
                newF.add(base + (free[0], free[1]))
                newF.add(base + (free[1], free[0]))
            else:
                for perm in ((1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1)):
                    newF.add(base + perm)
        frontier = [frontier[i] for i in keep] + new_edges
        processed.add(v)
        F = newF
        w = len(frontier)
        op = {0: "start", 1: "split", 2: "merge", 3: "close"}[len(old_pos)]
        if w == 0:
            steps.append((op, 0, 1.0, True))
            continue
        in_inv = sum(1 for x in F if not (w % 2 == 0 and len(set(x)) == 1))
        steps.append((op, w, len(F) / admissible_count(w), in_inv == invariant_size(w)))
    return steps


def faces(G):
    ok, emb = nx.check_planarity(G)
    seen, out = set(), []
    for u, v in sorted(emb.edges()):
        if (u, v) in seen:
            continue
        out.append(emb.traverse_face(u, v, mark_half_edges=seen))
    return out


def c60():
    ico = nx.icosahedral_graph()
    ok, emb = nx.check_planarity(ico)
    G = nx.Graph()
    for v in ico.nodes():
        nb = list(emb.neighbors_cw_order(v))
        for i, u in enumerate(nb):
            G.add_edge((v, u), (v, nb[(i + 1) % len(nb)]))
            G.add_edge((v, u), (u, v))
    return nx.convert_node_labels_to_integers(G, ordering="sorted")


def from_ascii(line):
    n, rest = line.split(b" ", 1)
    G = nx.Graph()
    for u, nb in enumerate(rest.strip().split(b",")):
        for c in nb:
            G.add_edge(u, c - 97)
    return G


def profile(steps):
    row = []
    for i, (op, w, d, h) in enumerate(steps):
        row.append(f"{i:2d} {op[:2]} w{w:2d} {d:.3f}{'*' if h else ' '}")
        if len(row) == 6:
            print("  " + "  ".join(row))
            row = []
    if row:
        print("  " + "  ".join(row))


def first_hold(steps):
    return next((i for i in range(4, len(steps)) if steps[i][3] and steps[i][1] >= 6), None)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "c60"
    if mode == "c60":
        G = c60()
        P = next(f for f in faces(G) if len(f) == 5)
        profile(sweep(G, P))
    elif mode == "witnesses":
        here = os.path.dirname(os.path.abspath(__file__))
        path = sys.argv[2] if len(sys.argv) > 2 else os.path.join(here, "exceptional_pentagons.json")
        for r in json.load(open(path)):
            G = nx.Graph([(u, v) for u, nb in enumerate(r["rotation"]) for v in nb])
            steps = sweep(G, r["face"])
            print(f"map {r['map']} (n={r['n']}) face {r['face']}: max width {max(s[1] for s in steps)}, "
                  f"first mid-sweep fullness at step {first_hold(steps)}, final density {steps[-1][2]:.3f}")
    elif mode == "stats":
        first_w, lapses, finals, never, maps = [], Counter(), [], 0, 0
        for line in sys.stdin.buffer:
            G = from_ascii(line)
            P = next(f for f in faces(G) if len(f) == 5)
            steps = sweep(G, P)
            maps += 1
            finals.append(steps[-1][2])
            idx = first_hold(steps)
            if idx is None:
                never += 1
                continue
            first_w.append(steps[idx][1])
            run = 0
            for s in steps[idx:]:
                if s[3]:
                    if run:
                        lapses[run] += 1
                    run = 0
                else:
                    run += 1
            if run:
                lapses[run] += 1
        print(f"maps={maps}; full mid-sweep at width>=6: {maps - never}; never: {never}")
        print("width of first mid-sweep fullness:", sorted(Counter(first_w).items()))
        print("lapse runs after first fullness (length: count):", sorted(lapses.items()))
        print("final densities below 1:", sum(1 for f in finals if f < 1),
              "minimum final density:", min(finals) if finals else None)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
