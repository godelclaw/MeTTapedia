"""Rooted-branch-decomposition width (the stack's middle-set measure) via a
caterpillar over a BFS-ordered edge list: an upper bound on the width of
the best decomposition.  Families: (5,0)-tubes with 0/1/3 Stone-Wales
dislocations (corridors), Goldberg GP(k,0) (spheres/walls).
Pre-registered: DW1 = tube widths stay bounded (~11) with and without
defects while GP(k,0) widths grow with k; DW2 = otherwise."""
import json, math, random
from collections import defaultdict, deque
from defected_tube_sweep_lab import zigzag_tube_rot
from wall_flower_lab import sw_rotate
from cut_chain_lab import goldberg_map

def caterpillar_width(n, edges, start_vertices, tries=3, seed=0):
    inc = defaultdict(list)
    for k, (u, v) in enumerate(edges): inc[u].append(k); inc[v].append(k)
    adj = defaultdict(set)
    for u, v in edges: adj[u].add(v); adj[v].add(u)
    def middle_count(prefix_set):
        return sum(1 for v in range(n) if any(k in prefix_set for k in inc[v]) and any(k not in prefix_set for k in inc[v]))
    best = None
    rng = random.Random(seed)
    for t in range(tries):
        # BFS vertex order from a start vertex; edge order = by (max BFS index of endpoints, min)
        s0 = rng.choice(list(start_vertices)) if t else min(start_vertices)
        dist = {s0: 0}; q = deque([s0]); order = []
        while q:
            x = q.popleft(); order.append(x)
            for y in sorted(adj[x]):
                if y not in dist: dist[y] = dist[x] + 1; q.append(y)
        pos = {v: i for i, v in enumerate(order)}
        eorder = sorted(range(len(edges)), key=lambda k: (max(pos[edges[k][0]], pos[edges[k][1]]), min(pos[edges[k][0]], pos[edges[k][1]])))
        S = set(); w = 0
        for k in eorder[:-1]:
            S.add(k); w = max(w, middle_count(S))
        if best is None or w < best: best = w
    return best

rows = []
for c, h, k in [(5, 8, 0), (5, 8, 1), (5, 12, 0), (5, 12, 3), (5, 16, 0), (5, 16, 5)]:
    n, rot, A, B, vid = zigzag_tube_rot(c, h)
    rng = random.Random(7); done = 0; tries = 0
    while done < k and tries < 100:
        tries += 1; r = rng.randrange(2, h - 2); i = rng.randrange(c); s = rng.randrange(2)
        a = vid[(r, i, s)]; b = rot[a][rng.randrange(3)]
        if sw_rotate(rot, a, b): done += 1
    edges = sorted({(min(a, b), max(a, b)) for a in rot for b in rot[a]})
    w = caterpillar_width(n, edges, A)
    rows.append(dict(family=f"tube c={c} h={h} defects={done}", V=n, width=w)); print(rows[-1], flush=True)
for kk in [1, 2, 3, 4, 5]:
    M = goldberg_map(kk)
    w = caterpillar_width(M.n, M.edges, M.A)
    rows.append(dict(family=f"GP({kk},0)", V=M.n, width=w)); print(rows[-1], flush=True)
json.dump(rows, open('decomposition_width_results.json', 'w'), indent=1)
tubes = [r['width'] for r in rows if r['family'].startswith('tube')]; gp = [r['width'] for r in rows if r['family'].startswith('GP')]
print("OUTCOME:", "DW1" if max(tubes) <= 14 and gp[-1] > gp[0] + 6 else "DW2")
