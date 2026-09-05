"""Corridor lemma off the perfect family: a (c,0) zigzag tube with ONE
Stone-Wales bond rotation in the middle. Does a slab-exhaustive sweeping
path with bounded raw-prefix crossing still exist?  Sweep = DFS that
exhausts each BFS-ring (two layers) before entering the next; prefix
crossing measured at every position.  Pre-registered: DT1 = sweep exists
and max prefix crossing stays within +4 of the perfect tube's 7; DT2 =
no ring-exhaustive sweep exists or crossings grow -> the raw-prefix form
needs a different prefix notion on defected corridors."""
import sys, math, json
from collections import defaultdict, deque
from wall_flower_lab import sw_rotate, faces_of

def zigzag_tube_rot(c, h):
    vid = {}; pos = {}
    def v(r, i, s):
        key = (r, i % c, s)
        if key not in vid:
            vid[key] = len(vid); pos[vid[key]] = (2 * math.pi * (i % c + 0.5 * s) / c, r + 0.5 * s)   # (angle, height)
        return vid[key]
    edges = set()
    for r in range(h):
        for i in range(c):
            edges.add((v(r, i, 0), v(r, i, 1))); edges.add((v(r, i, 1), v(r, i + 1, 0)))
            if r + 1 < h: edges.add((v(r, i, 1), v(r + 1, i + 1, 0)))
    n = len(vid)
    nb = defaultdict(list)
    for a, b in edges: nb[a].append(b); nb[b].append(a)
    rot = {}
    for x in range(n):
        th, z = pos[x]
        def ang(y):
            ty, zy = pos[y]; d = (ty - th + math.pi) % (2 * math.pi) - math.pi
            return math.atan2(zy - z, d)
        rot[x] = sorted(nb[x], key=ang)
    A = [vid[(0, i, 0)] for i in range(c)]; B = [vid[(h - 1, i, 1)] for i in range(c)]
    return n, rot, A, B, vid

def sweep_and_measure(n, rot, A, label):
    adj = {x: set(rot[x]) for x in rot}
    edges = {(min(a, b), max(a, b)) for a in rot for b in rot[a]}
    dist = {a: 0 for a in A}; q = deque(A)
    while q:
        x = q.popleft()
        for y in adj[x]:
            if y not in dist: dist[y] = dist[x] + 1; q.append(y)
    ring_of = {x: dist[x] // 2 for x in dist}
    ringsets = defaultdict(set)
    for x, r in ring_of.items(): ringsets[r].add(x)
    sys.setrecursionlimit(20000)
    best = None
    for s0 in sorted(A):
        path = [s0]; visited = {s0}; calls = [0]
        def dfs(cur, r):
            calls[0] += 1
            if calls[0] > 2_000_000: return False
            if len(visited) == n: return True
            remaining = ringsets[r] - visited
            target_r = r if remaining else r + 1
            for w in sorted(adj[cur]):
                if w not in visited and ring_of.get(w) == target_r:
                    visited.add(w); path.append(w)
                    if dfs(w, target_r): return True
                    visited.discard(w); path.pop()
            return False
        if dfs(s0, ring_of[s0]):
            best = list(path); break
    if best is None:
        print(f"{label}: NO ring-exhaustive sweep found (V={n})"); return None
    pre = set(); cross = []
    for x in best:
        pre.add(x); cross.append(sum(1 for (a, b) in edges if (a in pre) != (b in pre)))
    bidx = [t for t in range(len(best) - 1) if ring_of[best[t + 1]] != ring_of[best[t]]]
    print(f"{label}: V={n} sweep ok; ring-boundary positions {len(bidx)}; crossing at boundaries {[cross[t] for t in bidx]}; max anywhere {max(cross)}")
    return dict(V=n, boundaries=len(bidx), boundary_cross=[cross[t] for t in bidx], max_cross=max(cross))

out = {}
for c, h in [(5, 8), (5, 12)]:
    n, rot, A, B, vid = zigzag_tube_rot(c, h)
    sizes = sorted(len(f) for f in faces_of(rot))
    out[f'perfect c{c} h{h}'] = sweep_and_measure(n, rot, A, f"perfect tube c={c} h={h} (faces {set(sizes)})")
    # one Stone-Wales rotation on a mid-tube zig bond
    r0 = h // 2; a, b = vid[(r0, 0, 0)], vid[(r0, 0, 1)]
    ok = sw_rotate(rot, a, b)
    sizes2 = [len(f) for f in faces_of(rot)]
    from collections import Counter
    out[f'defect c{c} h{h}'] = sweep_and_measure(n, rot, A, f"defected tube c={c} h={h} (rotation {ok}; faces {dict(Counter(s for s in sizes2 if s < 30))})")
json.dump(out, open('defected_tube_sweep_results.json', 'w'), indent=1)
res = [r for r in out.values()]
print("OUTCOME:", "DT1" if all(r and r['max_cross'] <= 11 for r in res) else "DT2")
