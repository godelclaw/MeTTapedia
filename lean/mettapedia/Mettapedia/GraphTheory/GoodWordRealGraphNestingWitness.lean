import Mathlib

/-!
# A real-graph good-word closed web refuting sector-alternation drainage

The closed-web graph of Addendum XXVII(i) is a totally closed web at a
good word.  This module records one such web on one of the manuscript's
own census graphs — the C30 (5,0)-tube with the two vertex-disjoint
pentagon caps 2 and 13 (not the polar pair) — and checks in the kernel,
from explicit list data, that:

* the colouring is proper and totally closed (Addendum VIII), with the
  Kempe strands supplied and verified as the component partition;
* the inner word `1 2 0 0 0` is a good word: three consecutive
  majority spokes and one spoke of each other colour;
* the two rails (the non-`a` colours) are pendant-to-pendant paths
  covering every internal vertex, and the face labelling is exactly the
  two-sector partition of the annulus cut along the rails;
* on rail 1 the chord with edge id `26` strictly contains the chord with
  edge id `25` and both lie in the same sector, and the interior vertex
  `18` of the outer chord sends its `α`-edge (edge `25`) strictly inside
  the outer chord's sub-arc in the same sector; hence the universal
  drainage predicate is `false`.

The verifiers are those of `ClosedWebSectorNestingWitness`; only the
specimen differs.  The specimen was found by an exhaustive sweep of all
vertex-disjoint cap pairs of C30 (60 of the 120 good-word closed webs
carry such a nest).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.GoodWordRealGraphNestingWitness

/-! ## The specimen -/

/-- Tangle edges of the C30 two-hole tangle at caps 2,13, indexed `0..34`. -/
def tedges : List (Nat × Nat) := [(0, 2), (1, 4), (2, 3), (2, 13), (3, 4), (3, 15), (4, 17), (5, 6), (6, 9), (6, 29), (7, 8), (8, 9), (8, 26), (9, 28), (10, 14), (11, 19), (12, 20), (13, 14), (13, 16), (14, 23), (15, 16), (15, 18), (16, 25), (17, 18), (17, 19), (18, 27), (19, 21), (21, 22), (21, 29), (23, 24), (23, 26), (25, 26), (25, 28), (27, 28), (27, 29)]

/-- The closed-web colouring (colour of edge `i`). -/
def color : List Nat := [0, 1, 1, 2, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 2, 0, 1, 0, 2, 2, 1, 1, 2, 1, 0, 0, 2, 1, 0, 1, 0, 2, 1, 2]

/-- The distinguished colour `a` (the majority colour of the good word). -/
def aColor : Nat := 0

/-- Inner-hole and outer-hole spoke edges (in the cyclic order of the cap), and the pendant vertices. -/
def innerSpokes : List Nat := [7, 27, 16, 29, 10]
def outerSpokes : List Nat := [0, 1, 15, 16, 14]
def innerCap : List Nat := [5, 22, 20, 24, 7]
def outerCap : List Nat := [0, 1, 11, 12, 10]

/-- The two rails (vertex sequences), pendant to pendant; the nest lies on `rail1`. -/
def rail0 : List Nat := [1, 4, 3, 2, 13, 14, 23, 26, 8, 9, 6, 5]
def rail1 : List Nat := [11, 19, 17, 18, 15, 16, 25, 28, 27, 29, 21, 22]

/-- The 15 annulus faces, each as its list of tangle edge ids. -/
def faces : List (List Nat) := [[1, 4, 2, 0], [7, 8, 11, 10], [0, 3, 17, 14], [2, 5, 20, 18, 3], [4, 6, 23, 21, 5], [15, 24, 6, 1], [15, 26, 27, 16], [16, 29, 19, 14], [18, 22, 31, 30, 19, 17], [20, 22, 32, 33, 25, 21], [23, 25, 34, 28, 26, 24], [27, 28, 9, 7], [10, 12, 30, 29], [11, 13, 32, 31, 12], [8, 13, 33, 34, 9]]

/-- The claimed sector label of each face. -/
def sectorLabel : List Nat := [0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1]

/-! ## Elementary accessors -/

def edgeAt (i : Nat) : Nat × Nat := tedges.getD i (0, 0)
def colorAt (i : Nat) : Nat := color.getD i 0
def numEdges : Nat := tedges.length
def edgeIds : List Nat := List.range numEdges

def touchesVertex (i v : Nat) : Bool :=
  (edgeAt i).1 == v || (edgeAt i).2 == v

def edgesAtVertex (v : Nat) : List Nat :=
  edgeIds.filter (fun i => touchesVertex i v)

def isPendant (v : Nat) : Bool := innerCap.contains v || outerCap.contains v

def isRailEdge (i : Nat) : Bool := colorAt i != aColor

/-! ## Proper colouring -/

def properAtVertex (v : Nat) : Bool :=
  let es := edgesAtVertex v
  es.all fun i => es.all fun j => i == j || colorAt i != colorAt j

def isProper : Bool := (List.range 30).all properAtVertex

/-! ## Kempe strands and total closure (Addendum VIII)

The Kempe strands (two-colour components) are supplied as data and
verified: each strand is closed under coloured adjacency and connected,
and the strands of each pair partition that pair's edges.  A verified
partition of this kind is exactly the component partition. -/

/-- The strands of each colour pair, as lists of edge ids. -/
def strands01 : List (List Nat) := [[0, 2, 5, 10, 11, 13, 21, 25, 33], [1, 6, 7, 9, 24, 26, 28], [14, 17, 18, 22, 29, 30, 31], [16]]
def strands02 : List (List Nat) := [[0, 3, 4, 5, 6, 8, 9, 10, 12, 13, 18, 20, 23, 25, 31, 32, 34], [14, 19, 29], [15, 26, 27], [16]]
def strands12 : List (List Nat) := [[1, 2, 3, 4, 7, 8, 11, 12, 17, 19, 30], [15, 20, 21, 22, 23, 24, 27, 28, 32, 33, 34]]

def strandsOf (p q : Nat) : List (List Nat) :=
  if p == 0 && q == 1 then strands01
  else if p == 0 && q == 2 then strands02 else strands12

def inPair (p q e : Nat) : Bool := colorAt e == p || colorAt e == q

def sharesVertex (i j : Nat) : Bool :=
  touchesVertex j (edgeAt i).1 || touchesVertex j (edgeAt i).2

/-- Each pair's strands partition the pair's edges. -/
def strandsPartition (p q : Nat) : Bool :=
  edgeIds.all fun e =>
    let cnt := ((strandsOf p q).filter fun s => s.contains e).length
    if inPair p q e then cnt == 1 else cnt == 0

/-- Each strand is closed under coloured adjacency. -/
def strandsClosed (p q : Nat) : Bool :=
  (strandsOf p q).all fun s =>
    s.all fun e =>
      edgeIds.all fun j => !(inPair p q j && sharesVertex e j) || s.contains j

def expandWithin (s : List Nat) (cur : List Nat) : List Nat :=
  s.filter fun j => cur.contains j || cur.any fun i => sharesVertex i j

def reachWithin : Nat → List Nat → List Nat → List Nat
  | 0, _, cur => cur
  | n + 1, s, cur => reachWithin n s (expandWithin s cur)

/-- Each strand is connected. -/
def strandsConnected (p q : Nat) : Bool :=
  (strandsOf p q).all fun s =>
    match s with
    | [] => false
    | e :: _ => s.all (reachWithin s.length s [e]).contains

def strandsValid : Bool :=
  [(0, 1), (0, 2), (1, 2)].all fun pq =>
    strandsPartition pq.1 pq.2 && strandsClosed pq.1 pq.2 &&
      strandsConnected pq.1 pq.2

def innerTouching (s : List Nat) : Bool := innerSpokes.any s.contains

/-- The strand of edge `e` in pair `(p, q)`. -/
def strandOf (p q e : Nat) : List Nat :=
  ((strandsOf p q).filter fun s => s.contains e).headD []

/-- The other two colours of an edge. -/
def otherPairs (c : Nat) : List (Nat × Nat) :=
  if c == 0 then [(0, 1), (0, 2)] else if c == 1 then [(0, 1), (1, 2)]
  else [(0, 2), (1, 2)]

def strandTouch (e : Nat) (pq : Nat × Nat) : Bool :=
  innerTouching (strandOf pq.1 pq.2 e)

/-- An edge belongs to the web iff one of its strands is inner-touching. -/
def inWeb (e : Nat) : Bool := (otherPairs (colorAt e)).any (strandTouch e)

/-- Totally closed: every web edge has both strands inner-touching. -/
def totallyClosed : Bool :=
  edgeIds.all fun e => !inWeb e || (otherPairs (colorAt e)).all (strandTouch e)

/-! ## Rails and sectors -/

def consecutivePairs : List Nat → List (Nat × Nat)
  | [] => []
  | [_] => []
  | x :: y :: rest => (x, y) :: consecutivePairs (y :: rest)

def isEdgeOfColorNotA (u v : Nat) : Bool :=
  edgeIds.any fun i =>
    isRailEdge i && ((edgeAt i == (u, v)) || (edgeAt i == (v, u)))

def isRailPath (r : List Nat) : Bool :=
  (consecutivePairs r).all (fun p => isEdgeOfColorNotA p.1 p.2) &&
    isPendant (r.headD 0) && isPendant (r.getLastD 0)

/-- Every internal vertex lies on exactly one rail. -/
def railsCover : Bool :=
  (List.range 30).all fun v =>
    isPendant v || (rail0.contains v != rail1.contains v)

def facesOf (e : Nat) : List Nat :=
  (List.range faces.length).filter fun f => (faces.getD f []).contains e

def labelOf (f : Nat) : Nat := sectorLabel.getD f 0

/-- Labels agree across non-rail edges and differ across rail edges. -/
def labelsRespectRails : Bool :=
  edgeIds.all fun e =>
    match facesOf e with
    | [f, g] => if isRailEdge e then labelOf f != labelOf g
                else labelOf f == labelOf g
    | _ => true

def faceAdjNonRail (f g : Nat) : Bool :=
  edgeIds.any fun e =>
    !isRailEdge e && (faces.getD f []).contains e && (faces.getD g []).contains e

def expandFaces (cur : List Nat) : List Nat :=
  (List.range faces.length).filter fun g =>
    cur.contains g || cur.any fun f => faceAdjNonRail f g

def reachFuel : Nat → List Nat → List Nat
  | 0, cur => cur
  | n + 1, cur => reachFuel n (expandFaces cur)

/-- Each label class is connected through non-rail face adjacency. -/
def labelClassesConnected : Bool :=
  [0, 1].all fun l =>
    match (List.range faces.length).filter (fun f => labelOf f == l) with
    | [] => false
    | f :: rest =>
        let r := reachFuel 20 [f]
        rest.all r.contains && r.all (fun g => labelOf g == l)

/-! ## The nested same-sector chords -/

def railPos (v : Nat) : Nat := rail1.idxOf v

/-- A same-path chord on rail 1: an `a`-edge with both endpoints internal
and on rail 1. -/
def isRail1Chord (e : Nat) : Bool :=
  colorAt e == aColor && rail1.contains (edgeAt e).1 &&
    rail1.contains (edgeAt e).2 && !isPendant (edgeAt e).1 &&
    !isPendant (edgeAt e).2

def chordLo (e : Nat) : Nat := min (railPos (edgeAt e).1) (railPos (edgeAt e).2)
def chordHi (e : Nat) : Nat := max (railPos (edgeAt e).1) (railPos (edgeAt e).2)

def chordSector (e : Nat) : Nat := labelOf ((facesOf e).headD 0)

def chordFacesSameSector (e : Nat) : Bool :=
  (facesOf e).all fun f => labelOf f == chordSector e

/-- The `α`-edge of an internal vertex. -/
def alphaEdgeAt (v : Nat) : Nat :=
  ((edgesAtVertex v).filter fun e => colorAt e == aColor).headD 0

def otherEnd (e v : Nat) : Nat :=
  if (edgeAt e).1 == v then (edgeAt e).2 else (edgeAt e).1

/-- Universal drainage at one chord: every interior vertex's `α`-edge
leaves the disk — it is not a same-sector chord landing strictly inside
the sub-arc. -/
def chordDrains (e : Nat) : Bool :=
  (List.range rail1.length).all fun pos =>
    !(chordLo e < pos && pos < chordHi e) ||
      (let v := rail1.getD pos 0
       let f := alphaEdgeAt v
       let w := otherEnd f v
       !(isRail1Chord f && chordLo e < railPos w && railPos w < chordHi e &&
          chordSector f == chordSector e))

/-- The universal Sector-Alternation drainage claim on this web. -/
def universalDrainage : Bool :=
  edgeIds.all fun e => !isRail1Chord e || chordDrains e


/-! ## The good word -/

def cyc (w : List Nat) (i : Nat) : Nat := w.getD (i % w.length) 99
/-- colours of the inner spokes in the cap's cyclic order -/
def innerWord : List Nat := innerSpokes.map colorAt
/-- three consecutive spokes of the majority colour, one spoke of each other colour -/
def goodWord (w : List Nat) : Bool :=
  w.length == 5 && w.count aColor == 3 &&
  ((List.range 3).filter fun c => c != aColor).all (fun c => w.count c == 1) &&
  (List.range 5).any fun s => cyc w s == aColor && cyc w (s + 1) == aColor && cyc w (s + 2) == aColor

/-! ## The kernel-checked facts -/

theorem isProper_true : isProper = true := by decide
theorem strandsValid_true : strandsValid = true := by decide
theorem totallyClosed_true : totallyClosed = true := by decide
theorem innerWord_eq : innerWord = [1, 2, 0, 0, 0] := by decide
theorem innerWord_good : goodWord innerWord = true := by decide
theorem rails_true :
    (isRailPath rail0 && isRailPath rail1 && railsCover) = true := by decide
theorem sectors_true :
    (labelsRespectRails && labelClassesConnected) = true := by decide

/-- The two chords are nested on rail 1 and lie in one sector. -/
theorem nested_same_sector :
    (isRail1Chord 26 && isRail1Chord 25 &&
      chordLo 26 < chordLo 25 && chordHi 25 < chordHi 26 &&
      chordFacesSameSector 26 && chordFacesSameSector 25 &&
      chordSector 26 == chordSector 25) = true := by decide

/-- **Universal drainage fails at a good word on a real graph**: chord `26`
does not drain — its interior vertex `18` sends its `α`-edge `25` inside
the disk, in the same sector. -/
theorem universalDrainage_false : universalDrainage = false := by decide
theorem chord26_not_drains : chordDrains 26 = false := by decide

end Mettapedia.GraphTheory.GoodWordRealGraphNestingWitness
