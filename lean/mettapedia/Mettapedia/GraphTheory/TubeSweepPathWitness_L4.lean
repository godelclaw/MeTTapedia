/-!
# A sweeping path with bounded prefix crossings on the (5,0)-tube annulus of length 4

The sealed pumping bound counts positions along a simple path at which the
raw prefix (the path vertices visited so far) has at most `bound` crossing
edges. This module certifies, on the (5,0)-tube annulus of length 4
(50 vertices, cap pendants removed), a simple path through every vertex
whose prefix crossing count is at most 5 at each of the 4 ring-boundary
positions and at most 7 at every position. Decided by the kernel.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.TubeSweepPathWitness_L4

def nV : Nat := 50
def edges : List (Nat × Nat) := [(0, 2), (0, 4), (1, 2), (1, 9), (2, 10), (3, 4), (3, 6), (4, 13), (5, 6), (5, 8), (6, 15), (7, 8), (7, 9), (8, 17), (9, 11), (10, 12), (10, 14), (11, 12), (11, 19), (12, 20), (13, 14), (13, 16), (14, 23), (15, 16), (15, 18), (16, 25), (17, 18), (17, 19), (18, 27), (19, 21), (20, 22), (20, 24), (21, 22), (21, 29), (22, 30), (23, 24), (23, 26), (24, 33), (25, 26), (25, 28), (26, 35), (27, 28), (27, 29), (28, 37), (29, 31), (30, 32), (30, 34), (31, 32), (31, 39), (32, 40), (33, 34), (33, 36), (34, 43), (35, 36), (35, 38), (36, 45), (37, 38), (37, 39), (38, 47), (39, 41), (40, 42), (40, 44), (41, 42), (41, 49), (43, 44), (43, 46), (45, 46), (45, 48), (47, 48), (47, 49)]
/-- the sweeping path as a vertex sequence -/
def path : List Nat := [42, 40, 44, 43, 46, 45, 48, 47, 49, 41, 39, 37, 38, 35, 36, 33, 34, 30, 32, 31, 29, 27, 28, 25, 26, 23, 24, 20, 22, 21, 19, 17, 18, 15, 16, 13, 14, 10, 12, 11, 9, 1, 2, 0, 4, 3, 6, 5, 8, 7]
/-- prefix lengths at ring boundaries -/
def boundaries : List Nat := [10, 20, 30, 40]

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
  boundaries.length == 4 && boundaries.all fun k => 0 < k && k < nV && prefixCrossing k ≤ 5
def everywhereOk : Bool := (List.range (nV + 1)).all fun k => prefixCrossing k ≤ 7

theorem isSweep_true : isSweep = true := by decide
theorem boundaries_true : boundariesOk = true := by decide
theorem everywhere_true : everywhereOk = true := by decide

end Mettapedia.GraphTheory.TubeSweepPathWitness_L4
