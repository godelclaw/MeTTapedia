import Mathlib

/-!
# A good-word totally closed web with a same-side nested chord pair

The Sector-Alternation Lemma for the closed-web graph `B₁ ∪ B₂ ∪ α` at a
good word claims that every chord with both endpoints on one rail bounds a
disk out of which every interior rail vertex drains its `α`-edge, so that
nested chords alternate sides.  This module records one finite annular
tangle on which that claim is false, with every fact decided by the kernel
from explicit list data:

* a cubic annular tangle with 14 internal vertices and five stubs at each
  hole, given by its counterclockwise rotation system; the faces of the
  rotation system are supplied and verified (each face follows the
  rotation rule and the faces partition the darts), the Euler
  characteristic is that of the sphere, exactly two faces carry stubs and
  each of them gathers exactly its own five stubs, and every interior face
  has length at least five;
* a proper 3-edge-colouring whose inner word is the good word `1 2 0 0 0`;
* every two-colour Kempe component is supplied as data and verified to be
  a path from an inner stub to an outer stub (all strands radial: total
  closure at a good word);
* the two rails (the non-`α` paths) are pendant-to-pendant and cover the
  internal vertices;
* on the second rail the chords `(5,13)` and `(7,11)` are nested (rail
  positions `4 < 6 < 10 < 12`) and attach on the same side by the
  rotation, and the interior vertex `7` of the outer chord has its
  `α`-edge landing at `11`, strictly inside the outer chord's interval on
  the same side; hence the universal drainage predicate is `false`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.GoodWordClosedWebNestingWitness

/-- internal vertices 0..13; stubs 14=IB1 15=IB2 16=OB1 17=OB2 18..20=Ia0..2 21..23=Oa0..2 -/
def nV : Nat := 24
def edges : List (Nat × Nat) := [(14, 0), (0, 1), (1, 16), (15, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10), (10, 11), (11, 12), (12, 13), (13, 17), (11, 7), (13, 5), (21, 3), (0, 2), (12, 22), (10, 23), (9, 1), (8, 20), (6, 19), (4, 18)]
def color : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- counterclockwise rotation at every vertex (stubs have one neighbour) -/
def rot : List (List Nat) := [[14, 2, 1], [0, 16, 9], [15, 3, 0], [2, 4, 21], [3, 18, 5], [4, 6, 13], [5, 19, 7], [6, 8, 11], [7, 20, 9], [8, 1, 10], [9, 23, 11], [10, 12, 7], [11, 22, 13], [12, 17, 5], [0], [2], [1], [13], [4], [6], [8], [3], [12], [10]]
/-- the faces of the rotation system as vertex cycles -/
def faces : List (List Nat) := [[0, 14, 0, 2, 15, 2, 3, 4, 18, 4, 5, 6, 19, 6, 7, 8, 20, 8, 9, 1], [0, 1, 16, 1, 9, 10, 23, 10, 11, 12, 22, 12, 13, 17, 13, 5, 4, 3, 21, 3, 2], [5, 13, 12, 11, 7, 6], [7, 11, 10, 9, 8]]
def innerStubs : List Nat := [14, 15, 18, 19, 20]
def outerStubs : List Nat := [16, 17, 21, 22, 23]
def railB1 : List Nat := [14, 0, 1, 16]
def railB2 : List Nat := [15, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17]
def strands01 : List (List Nat) := [[0, 4, 18, 19], [2, 10, 22, 23], [6, 14, 17, 20, 25], [8, 12, 16, 21, 24]]
def strands02 : List (List Nat) := [[1, 3, 11, 19, 21, 22], [5, 18, 25], [7, 15, 17, 24], [9, 13, 16, 20, 23]]
def strands12 : List (List Nat) := [[0, 1, 2], [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]

/-! ## Basic accessors -/

def nE : Nat := edges.length
def edgeAt (e : Nat) : Nat × Nat := edges.getD e (999, 999)
def colorAt (e : Nat) : Nat := color.getD e 99
def rotAt (v : Nat) : List Nat := rot.getD v []
def incident (v e : Nat) : Bool := (edgeAt e).1 == v || (edgeAt e).2 == v
def other (v e : Nat) : Nat := if (edgeAt e).1 == v then (edgeAt e).2 else (edgeAt e).1
def sharesVertex (e f : Nat) : Bool := incident (edgeAt e).1 f || incident (edgeAt e).2 f
def edgeIdOf (u v : Nat) : Nat :=
  ((List.range nE).find? fun e => edgeAt e == (u, v) || edgeAt e == (v, u)).getD 999
def adjacent (u v : Nat) : Bool := edgeIdOf u v < nE
def neighbors (v : Nat) : List Nat :=
  (List.range nE).filterMap fun e => if incident v e then some (other v e) else none
def isStub (v : Nat) : Bool := innerStubs.contains v || outerStubs.contains v

/-! ## Proper colouring and degrees -/

def colorsValid : Bool := color.length == nE && color.all (· < 3)

def isProper : Bool :=
  (List.range nE).all fun e => (List.range nE).all fun f =>
    e == f || !(sharesVertex e f) || colorAt e != colorAt f

def degreesValid : Bool :=
  (List.range nV).all fun v =>
    if isStub v then (neighbors v).length == 1 else (neighbors v).length == 3

/-! ## Rotation system and faces -/

def idxOfAux : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | x :: xs, u, i => if x == u then i else idxOfAux xs u (i + 1)

/-- the neighbour following `u` counterclockwise around `v` -/
def rotSucc (v u : Nat) : Nat :=
  let r := rotAt v
  r.getD ((idxOfAux r u 0 + 1) % r.length) 999

def rotValid : Bool :=
  rot.length == nV && (List.range nV).all fun v =>
    let r := rotAt v
    let nb := neighbors v
    r.length == nb.length && nb.all r.contains && r.eraseDups.length == r.length

def cyc (f : List Nat) (i : Nat) : Nat := f.getD (i % f.length) 999

/-- each consecutive dart pair of a face obeys the rotation rule -/
def faceValid (f : List Nat) : Bool :=
  f.length ≥ 1 && (List.range f.length).all fun i => cyc f (i + 2) == rotSucc (cyc f (i + 1)) (cyc f i)

def faceDarts (f : List Nat) : List (Nat × Nat) :=
  (List.range f.length).map fun i => (cyc f i, cyc f (i + 1))

def allDarts : List (Nat × Nat) := faces.foldr (fun f acc => faceDarts f ++ acc) []

/-- the supplied faces use every dart of the rotation system exactly once -/
def dartsValid : Bool :=
  allDarts.length == (List.range nV).foldr (fun v acc => (rotAt v).length + acc) 0 &&
  allDarts.eraseDups.length == allDarts.length &&
  allDarts.all fun d => (rotAt d.1).contains d.2

def facesValid : Bool := faces.all faceValid && dartsValid

def holeFaces : List (List Nat) := faces.filter fun f => f.any isStub
def interiorFaces : List (List Nat) := faces.filter fun f => !(f.any isStub)

/-- two hole faces, each gathering exactly its own five stubs; interior faces of length ≥ 5 -/
def holesValid : Bool :=
  holeFaces.length == 2 &&
  holeFaces.any (fun f => innerStubs.all f.contains && !(f.any fun v => outerStubs.contains v)) &&
  holeFaces.any (fun f => outerStubs.all f.contains && !(f.any fun v => innerStubs.contains v)) &&
  interiorFaces.all fun f => f.length ≥ 5

/-! ## The inner word -/

def stubColor (s : Nat) : Nat := colorAt (edgeIdOf s ((rotAt s).getD 0 999))
def innerHoleFace : List Nat := (holeFaces.find? fun f => innerStubs.all f.contains).getD []
/-- colours of the inner stubs in the cyclic order of the inner hole face -/
def innerWord : List Nat := (innerHoleFace.filter fun v => innerStubs.contains v).map stubColor

def goodWord (w : List Nat) : Bool :=
  w.length == 5 && w.count 0 == 3 && w.count 1 == 1 && w.count 2 == 1 &&
  (List.range 5).any fun s => cyc w s == 0 && cyc w (s + 1) == 0 && cyc w (s + 2) == 0

/-! ## Kempe strands: supplied and verified radial -/

def inPair (a b e : Nat) : Bool := colorAt e == a || colorAt e == b

def strandVerts (s : List Nat) : List Nat :=
  (s.foldr (fun e acc => (edgeAt e).1 :: (edgeAt e).2 :: acc) []).eraseDups
def degIn (s : List Nat) (v : Nat) : Nat := (s.filter fun e => incident v e).length
def ends (s : List Nat) : List Nat := (strandVerts s).filter fun v => degIn s v == 1

def grow (s : List Nat) (reach : List Nat) : List Nat :=
  (s.foldr (fun e acc =>
    if reach.contains (edgeAt e).1 || reach.contains (edgeAt e).2 then
      (edgeAt e).1 :: (edgeAt e).2 :: acc else acc) reach).eraseDups
def reachN : Nat → List Nat → List Nat → List Nat
  | 0, _, r => r
  | n + 1, s, r => reachN n s (grow s r)
def strandConnected (s : List Nat) : Bool :=
  let vs := strandVerts s
  vs.all fun v => (reachN vs.length s [vs.getD 0 999]).contains v

/-- a connected acyclic edge set whose two degree-one vertices are one inner and one outer stub -/
def radialPath (s : List Nat) : Bool :=
  let vs := strandVerts s
  let es := ends s
  s.length + 1 == vs.length && strandConnected s && es.length == 2 &&
  ((innerStubs.contains (es.getD 0 999) && outerStubs.contains (es.getD 1 999)) ||
   (innerStubs.contains (es.getD 1 999) && outerStubs.contains (es.getD 0 999)))

/-- the supplied strands partition the `{a,b}`-edges, are closed under `{a,b}`-adjacency
(hence are the Kempe components), and are all radial -/
def strandsValid (a b : Nat) (ss : List (List Nat)) : Bool :=
  ((List.range nE).all fun e => !(inPair a b e) || (ss.filter fun s => s.contains e).length == 1) &&
  (ss.all fun s => s.all fun e => inPair a b e &&
    (List.range nE).all fun f => !(inPair a b f) || !(sharesVertex e f) || s.contains f) &&
  ss.all radialPath

def allStrandsRadial : Bool :=
  strandsValid 0 1 strands01 && strandsValid 0 2 strands02 && strandsValid 1 2 strands12

/-! ## Rails, sides, chords, drainage -/

def railValid (r : List Nat) : Bool :=
  r.length ≥ 2 && innerStubs.contains (r.getD 0 999) && outerStubs.contains (r.getD (r.length - 1) 999) &&
  (List.range (r.length - 1)).all fun i =>
    adjacent (r.getD i 999) (r.getD (i + 1) 999) && colorAt (edgeIdOf (r.getD i 999) (r.getD (i + 1) 999)) != 0
def railInterior (r : List Nat) : List Nat := (r.drop 1).take (r.length - 2)

def railsValid : Bool :=
  railValid railB1 && railValid railB2 &&
  (railInterior railB1 ++ railInterior railB2).eraseDups.length == 14 &&
  (railInterior railB1 ++ railInterior railB2).all (· < 14) &&
  ((List.range nE).filter fun e => colorAt e != 0).length == (railB1.length - 1) + (railB2.length - 1)

def railPos (r : List Nat) (v : Nat) : Nat := idxOfAux r v 0
def onRail (r : List Nat) (v : Nat) : Bool := (railInterior r).contains v
def alphaNbr (v : Nat) : Nat :=
  ((neighbors v).find? fun w => colorAt (edgeIdOf v w) == 0).getD 999

/-- the `α`-edge at an interior rail vertex leaves on side S when, counterclockwise,
the rail's `down` neighbour is followed by its `up` neighbour -/
def sideS (r : List Nat) (v : Nat) : Bool :=
  rotSucc v (r.getD (railPos r v - 1) 999) == r.getD (railPos r v + 1) 999

/-- chords on a rail as position pairs `(lo, hi)` -/
def chordsOn (r : List Nat) : List (Nat × Nat) :=
  (railInterior r).filterMap fun v =>
    let x := alphaNbr v
    if onRail r x && railPos r v < railPos r x then some (railPos r v, railPos r x) else none

/-- the source's drainage claim for one chord: every interior rail vertex's `α`-edge
leaves the chord's disk (does not land strictly inside the interval on the same side) -/
def chordDrains (r : List Nat) (lo hi : Nat) : Bool :=
  (List.range (hi - lo - 1)).all fun k =>
    let w := r.getD (lo + 1 + k) 999
    let x := alphaNbr w
    !(onRail r x && lo < railPos r x && railPos r x < hi && sideS r w == sideS r (r.getD lo 999))

def universalDrainage : Bool :=
  (chordsOn railB1).all (fun c => chordDrains railB1 c.1 c.2) &&
  (chordsOn railB2).all (fun c => chordDrains railB2 c.1 c.2)

/-! ## The kernel-checked facts -/

theorem colorsValid_true : colorsValid = true := by decide
theorem isProper_true : isProper = true := by decide
theorem degreesValid_true : degreesValid = true := by decide
theorem rotValid_true : rotValid = true := by decide
theorem facesValid_true : facesValid = true := by decide
/-- `V - E + F = 2`: the rotation system with the holes filled is a sphere -/
theorem euler_sphere : nV + faces.length = nE + 2 := by decide
theorem holesValid_true : holesValid = true := by decide
theorem innerWord_eq : innerWord = [1, 2, 0, 0, 0] := by decide
theorem innerWord_good : goodWord innerWord = true := by decide
theorem allStrandsRadial_true : allStrandsRadial = true := by decide
theorem railsValid_true : railsValid = true := by decide
theorem chordsB1_eq : chordsOn railB1 = [] := by decide
/-- chords `(5,13)` and `(7,11)` at rail positions `(4,12)` and `(6,10)` -/
theorem chordsB2_eq : chordsOn railB2 = [(4, 12), (6, 10)] := by decide
theorem nested : 4 < 6 ∧ 10 < 12 := by decide
theorem same_side :
    (sideS railB2 5 && sideS railB2 13 && sideS railB2 7 && sideS railB2 11) = true := by decide
theorem chord_5_13_not_drains : chordDrains railB2 4 12 = false := by decide
theorem chord_7_11_drains : chordDrains railB2 6 10 = true := by decide
theorem universalDrainage_false : universalDrainage = false := by decide

end Mettapedia.GraphTheory.GoodWordClosedWebNestingWitness
