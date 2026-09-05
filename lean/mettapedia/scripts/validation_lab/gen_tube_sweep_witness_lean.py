"""Kernel witness: the (5,0)-tube annulus of length L (pendants removed) has a
simple sweeping path whose raw prefix has <= 5 crossing edges at each of the
L ring-boundary positions and <= 7 everywhere — the object the sealed
pumping bound consumes (positions along a path with bounded prefix crossing)."""
import sys, json
from collections import defaultdict
from cut_chain_growth import tube_map_nopendant
L = int(sys.argv[1]) if len(sys.argv) > 1 else 4
M = tube_map_nopendant(L)
adj = defaultdict(set)
for (u, v) in M.edges: adj[u].add(v); adj[v].add(u)
from collections import deque
dist = {v: 0 for v in M.A}; q = deque(M.A)
while q:
    x = q.popleft()
    for y in adj[x]:
        if y not in dist: dist[y] = dist[x] + 1; q.append(y)
ring_of = {v: dist[v] // 2 for v in dist}
ringsets = defaultdict(set)
for v, r in ring_of.items(): ringsets[r].add(v)
sys.setrecursionlimit(10000)
def sweep(start_v):
    path = [start_v]; visited = {start_v}
    def dfs(cur, r):
        if len(visited) == M.n: return True
        remaining = ringsets[r] - visited
        cands = [w for w in adj[cur] if w not in visited and (ring_of[w] == r if remaining else ring_of[w] == r + 1)]
        for w in cands:
            visited.add(w); path.append(w)
            if dfs(w, r + (0 if remaining else 1)): return True
            visited.discard(w); path.pop()
        return False
    return dfs(start_v, ring_of[start_v]), path
for s0 in sorted(M.A):
    ok, path = sweep(s0)
    if ok: break
assert ok and len(path) == M.n
boundaries = [t + 1 for t in range(len(path) - 1) if ring_of[path[t + 1]] != ring_of[path[t]]]   # cut = number of prefix vertices
def L_(xs): return '[' + ', '.join(str(x) for x in xs) + ']'
def LP(ps): return '[' + ', '.join(f'({a}, {b})' for a, b in ps) + ']'
mod = f"TubeSweepPathWitness_L{L}"
lean = f'''/-!
# A sweeping path with bounded prefix crossings on the (5,0)-tube annulus of length {L}

The sealed pumping bound counts positions along a simple path at which the
raw prefix (the path vertices visited so far) has at most `bound` crossing
edges. This module certifies, on the (5,0)-tube annulus of length {L}
({M.n} vertices, cap pendants removed), a simple path through every vertex
whose prefix crossing count is at most 5 at each of the {len(boundaries)} ring-boundary
positions and at most 7 at every position. Decided by the kernel.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.{mod}

def nV : Nat := {M.n}
def edges : List (Nat × Nat) := {LP(M.edges)}
/-- the sweeping path as a vertex sequence -/
def path : List Nat := {L_(path)}
/-- prefix lengths at ring boundaries -/
def boundaries : List Nat := {L_(boundaries)}

def adjacent (u v : Nat) : Bool := edges.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

/-- consecutive vertices adjacent, no repeats, every vertex visited -/
def isSweep : Bool :=
  path.length == nV && path.eraseDups.length == nV && path.all (· < nV) &&
  (List.range (path.length - 1)).all fun t => adjacent (path.getD t 999) (path.getD (t + 1) 999)

/-- crossing edges of the prefix of length `k` -/
def prefixCrossing (k : Nat) : Nat :=
  let pre := path.take k
  (edges.filter fun e => pre.contains e.1 != pre.contains e.2).length

def boundariesOk : Bool :=
  boundaries.length == {len(boundaries)} && boundaries.all fun k => 0 < k && k < nV && prefixCrossing k ≤ 5
def everywhereOk : Bool := (List.range (nV + 1)).all fun k => prefixCrossing k ≤ 7

theorem isSweep_true : isSweep = true := by decide
theorem boundaries_true : boundariesOk = true := by decide
theorem everywhere_true : everywhereOk = true := by decide

end Mettapedia.GraphTheory.{mod}
'''
out = f'/home/oruzi/repos/MeTTapedia-4cplab/lean/mettapedia/Mettapedia/GraphTheory/{mod}.lean'
open(out, 'w').write(lean); print("wrote", out, "V", M.n, "boundaries", len(boundaries))
