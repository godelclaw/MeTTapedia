"""Emit a Lean module certifying a nested chain of exact saturated separating
transversals of width <= b on a (5,0)-tube annulus (cap pendants removed).
Data: vertices, edges, the two boundary rings, the chain of crossed-edge
sets.  Every fact is a Bool verifier closed by `decide`."""
import sys, json
from cut_chain_lab import Map, longest_chain
from cut_chain_growth import tube_map_nopendant

L = int(sys.argv[1]) if len(sys.argv) > 1 else 4
b = int(sys.argv[2]) if len(sys.argv) > 2 else 6
M = tube_map_nopendant(L)
cyc = M.dual_cycles(b)
items = []
for (fs, es) in cyc:
    exact, sat, sep, mask = M.classify(es)
    if exact and sat and sep and len(es) <= b:
        items.append((mask, tuple(sorted(es))))
m, chain = longest_chain(items)
X = [list(k) for (_, k) in chain]
A = sorted(M.A); B = sorted(M.B)
print("tube L", L, "V", M.n, "E", len(M.edges), "b", b, "chain length", m, "widths", [len(x) for x in X])

def L_(xs): return '[' + ', '.join(str(x) for x in xs) + ']'
def LL(xss): return '[' + ', '.join(L_(x) for x in xss) + ']'
def LP(ps): return '[' + ', '.join(f'({u}, {v})' for u, v in ps) + ']'

OUT = '/home/oruzi/repos/MeTTapedia-4cplab/lean/mettapedia/Mettapedia/GraphTheory/TubeCutChainWitness.lean'
src = f'''import Mathlib

/-!
# A nested chain of exact saturated transversals on a (5,0)-tube annulus

The target-forced cut chain (the L1–splice junction of the compositional
route) needs, in a large instance, many pairwise nested transversals of
bounded width, each with an exact deletion side, each separating the two
designated holes, with every slab between consecutive transversals
containing a vertex.  This module certifies that geometric output on the
manuscript's own corridor family: the (5,0)-tube annulus of length {L}
({M.n} internal vertices after removing the cap pendants, holes = the two
boundary rings) carries a chain of {m} such transversals of width at most
{b}.  A transversal is given by its crossed-edge set; the kernel checks
from explicit data that each crossed set has width ≤ {b}, that deleting it
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

def nV : Nat := {M.n}
def edges : List (Nat × Nat) := {LP(M.edges)}
/-- the inner boundary ring (hole A) and the outer boundary ring (hole B) -/
def ringA : List Nat := {L_(A)}
def ringB : List Nat := {L_(B)}
/-- the chain of transversals, innermost first, each as its crossed-edge ids -/
def chain : List (List Nat) := {LL(X)}
def widthBound : Nat := {b}

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

theorem chain_length : chain.length = {m} := by decide
theorem chainValid_true : chainValid = true := by decide

end Mettapedia.GraphTheory.TubeCutChainWitness
'''
open(OUT, 'w').write(src)
print("wrote", OUT)
