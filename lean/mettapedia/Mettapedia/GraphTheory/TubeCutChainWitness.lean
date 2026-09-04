import Mathlib

/-!
# A nested chain of exact saturated transversals on a (5,0)-tube annulus

The target-forced cut chain (the L1–splice junction of the compositional
route) needs, in a large instance, many pairwise nested transversals of
bounded width, each with an exact deletion side, each separating the two
designated holes, with every slab between consecutive transversals
containing a vertex.  This module certifies that geometric output on the
manuscript's own corridor family: the (5,0)-tube annulus of length 4
(50 internal vertices after removing the cap pendants, holes = the two
boundary rings) carries a chain of 13 such transversals of width at most
6.  A transversal is given by its crossed-edge set; the kernel checks
from explicit data that each crossed set has width ≤ 6, that deleting it
leaves exactly two connected sides (the side reached from the inner ring
and the side reached from the outer ring, disjoint and covering every
vertex, every crossed edge joining them), that the crossed edges have
pairwise distinct endpoints (saturation), that the inner ring lies on the
inner side and the outer ring on the outer side, and that the inner sides
strictly increase along the chain.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.TubeCutChainWitness

def nV : Nat := 50
def edges : List (Nat × Nat) := [(0, 2), (0, 4), (1, 2), (1, 9), (2, 10), (3, 4), (3, 6), (4, 13), (5, 6), (5, 8), (6, 15), (7, 8), (7, 9), (8, 17), (9, 11), (10, 12), (10, 14), (11, 12), (11, 19), (12, 20), (13, 14), (13, 16), (14, 23), (15, 16), (15, 18), (16, 25), (17, 18), (17, 19), (18, 27), (19, 21), (20, 22), (20, 24), (21, 22), (21, 29), (22, 30), (23, 24), (23, 26), (24, 33), (25, 26), (25, 28), (26, 35), (27, 28), (27, 29), (28, 37), (29, 31), (30, 32), (30, 34), (31, 32), (31, 39), (32, 40), (33, 34), (33, 36), (34, 43), (35, 36), (35, 38), (36, 45), (37, 38), (37, 39), (38, 47), (39, 41), (40, 42), (40, 44), (41, 42), (41, 49), (43, 44), (43, 46), (45, 46), (45, 48), (47, 48), (47, 49)]
/-- the inner boundary ring (hole A) and the outer boundary ring (hole B) -/
def ringA : List Nat := [42, 44, 46, 48, 49]
def ringB : List Nat := [0, 1, 3, 5, 7]
/-- the chain of transversals, innermost first, each as its crossed-edge ids -/
def chain : List (List Nat) := [[49, 52, 55, 58, 59], [34, 47, 50, 55, 58, 59], [34, 37, 47, 53, 58, 59], [34, 37, 40, 47, 56, 59], [34, 37, 40, 43, 44], [19, 32, 35, 40, 43, 44], [19, 22, 32, 38, 43, 44], [19, 22, 25, 32, 41, 44], [19, 22, 25, 28, 29], [4, 17, 20, 25, 28, 29], [4, 7, 17, 23, 28, 29], [4, 7, 10, 17, 26, 29], [4, 7, 10, 13, 14]]
def widthBound : Nat := 6

def edgeAt (e : Nat) : Nat × Nat := edges.getD e (999, 999)

/-- one expansion step of reachability avoiding the crossed edges -/
def grow (X : List Nat) (cur : List Nat) : List Nat :=
  ((List.range edges.length).foldr (fun e acc =>
    if X.contains e then acc
    else
      let p := edgeAt e
      if cur.contains p.1 || cur.contains p.2 then p.1 :: p.2 :: acc else acc) cur).eraseDups

def reachN : Nat → List Nat → List Nat → List Nat
  | 0, _, cur => cur
  | n + 1, X, cur => reachN n X (grow X cur)

def sideA (X : List Nat) : List Nat := reachN nV X [ringA.getD 0 999]
def sideB (X : List Nat) : List Nat := reachN nV X [ringB.getD 0 999]

/-- deleting `X` leaves exactly the two connected sides, and every crossed edge joins them -/
def exact (X : List Nat) : Bool :=
  let a := sideA X
  let bb := sideB X
  a.all (fun v => !(bb.contains v)) && a.length + bb.length == nV &&
  X.all fun e => (a.contains (edgeAt e).1 && bb.contains (edgeAt e).2) ||
                 (a.contains (edgeAt e).2 && bb.contains (edgeAt e).1)

/-- the crossed edges have pairwise distinct endpoints -/
def saturated (X : List Nat) : Bool :=
  let ends := X.foldr (fun e acc => (edgeAt e).1 :: (edgeAt e).2 :: acc) []
  ends.eraseDups.length == ends.length

/-- hole A on the inner side, hole B on the outer side -/
def separating (X : List Nat) : Bool :=
  ringA.all (sideA X).contains && ringB.all (sideB X).contains

def widthOk (X : List Nat) : Bool := X.length ≤ widthBound && X.eraseDups.length == X.length

/-- consecutive inner sides strictly increase (so every slab holds a vertex) -/
def nested : List (List Nat) → Bool
  | X :: Y :: rest =>
      let a := sideA X
      let c := sideA Y
      a.all c.contains && a.length < c.length && nested (Y :: rest)
  | _ => true

def chainValid : Bool :=
  chain.all (fun X => widthOk X && exact X && saturated X && separating X) && nested chain

theorem chain_length : chain.length = 13 := by decide
theorem chainValid_true : chainValid = true := by decide

end Mettapedia.GraphTheory.TubeCutChainWitness
