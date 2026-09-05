"""Corridor-lemma interface gate on the (5,0)-tube annulus (pendants removed):
the sealed pumping bound counts positions along a simple PATH whose raw
prefix (vertices visited so far) has at most `bound` crossing edges.
Build a sweeping path: order vertices by distance from the inner ring, and
within each distance layer walk along the layer's cycle, moving to the
next layer at the end; then measure crossing edges of every prefix.
Pre-registered: TS1 = a simple sweeping path exists (adjacent consecutive
vertices) and prefix crossing at layer boundaries is <= 12 for all L;
TS2 = the greedy sweep fails to be a path or crossings grow with L."""
import sys, json
from collections import defaultdict, deque
from cut_chain_growth import tube_map_nopendant
out = {}
for L in [2, 4, 6, 8, 10, 14]:
    M = tube_map_nopendant(L)
    adj = defaultdict(set)
    for (u, v) in M.edges: adj[u].add(v); adj[v].add(u)
    # BFS layers from ring A
    dist = {v: 0 for v in M.A}; q = deque(M.A)
    while q:
        x = q.popleft()
        for y in adj[x]:
            if y not in dist: dist[y] = dist[x] + 1; q.append(y)
    layers = defaultdict(list)
    for v, d in dist.items(): layers[d].append(v)
    # ring-by-ring sweep: ring k = layers {2k, 2k+1}; find a simple path that exhausts each ring
    # before entering the next (DFS with backtracking inside the ring; entry from the previous ring's end)
    import sys as _s; _s.setrecursionlimit(10000)
    nrings = (max(layers) + 2) // 2
    ring_of = {v: dist[v] // 2 for v in dist}
    ringsets = defaultdict(set)
    for v, r in ring_of.items(): ringsets[r].add(v)
    def sweep(start_v):
        path = [start_v]; visited = {start_v}
        def dfs(cur, r):
            if len(visited) == M.n: return True
            remaining = ringsets[r] - visited
            if not remaining:
                # move to next ring
                for w in adj[cur]:
                    if w not in visited and ring_of[w] == r + 1:
                        visited.add(w); path.append(w)
                        if dfs(w, r + 1): return True
                        visited.discard(w); path.pop()
                return False
            for w in adj[cur]:
                if w not in visited and ring_of[w] == r:
                    visited.add(w); path.append(w)
                    if dfs(w, r): return True
                    visited.discard(w); path.pop()
            return False
        ok = dfs(start_v, ring_of[start_v])
        return ok, path
    ok = False
    for s0 in sorted(M.A):
        ok, path = sweep(s0)
        if ok: break
    # prefix crossing counts
    cross = []
    pos = set()
    for t, v in enumerate(path):
        pos.add(v)
        c = sum(1 for (a, b) in M.edges if (a in pos) != (b in pos))
        cross.append(c)
    boundary_idx = []
    seen_layers = set()
    for t, v in enumerate(path):
        if t + 1 < len(path) and ring_of[path[t + 1]] != ring_of[v]: boundary_idx.append(t)
    bcross = [cross[t] for t in boundary_idx]
    out[L] = dict(V=M.n, path_ok=ok and len(path) == M.n, layers=len(layers), max_cross=max(cross), max_boundary_cross=max(bcross) if bcross else None,
                  boundary_positions=len(boundary_idx), cross_at_boundaries=bcross[:12])
    print(f"L={L}: V={M.n} sweep path ok={out[L]['path_ok']} layers={len(layers)} boundary positions={len(boundary_idx)} max prefix crossing={max(cross)} at layer boundaries max={out[L]['max_boundary_cross']} sample={bcross[:8]}", flush=True)
json.dump(out, open('tube_sweep_path_results.json', 'w'), indent=1)
print("OUTCOME:", "TS1" if all(r['path_ok'] and r['max_boundary_cross'] is not None and r['max_boundary_cross'] <= 12 for r in out.values()) else "TS2")
