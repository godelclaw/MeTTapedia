import Mathlib

/-!
# A census closed web refuting universal sector-alternation drainage

The v24 working notes (Addendum XXVII(i)) claim that in the closed-web
graph `B1 ∪ B2 ∪ α` every same-path chord's disk drains: each interior
vertex of the chord's rail sub-arc sends its `α`-edge out of the disk to
the opposite sector, so same-sector nesting is impossible.  The
pre-registered small-case lab (`scripts/validation_lab/sector_alternation_lab.py`)
found the claim false on the census specimens the notes cite.  This
module makes one specimen kernel-checkable.

The data below is one of the 360 totally closed colourings of the C30
two-hole tangle (the (5,0)-tube minus its two polar pentagons).  Every
fact is a `Bool` computation on explicit lists, checked by `decide`:

* the colouring is proper on the tangle;
* it is totally closed in the sense of Addendum VIII (every edge of an
  inner-touching Kempe strand has both of its strands inner-touching);
* the two rails (the non-`a` colours) are pendant-to-pendant paths
  covering every internal vertex, and the face labelling is exactly the
  two-sector partition of the annulus cut along the rails (labels agree
  across every non-rail edge, differ across every rail edge, and each
  label class is connected);
* on rail 1 the three same-path chords `(19,21) ⊃ (12,20) ⊃ (14,23)`
  are nested with all their incident faces in the same sector, and the
  interior vertex `14` of chord `(12,20)` has its `α`-edge `(14,23)`
  landing inside the disk in the same sector: universal drainage fails.

This is a finite refutation of the universal statement.  It says nothing
against the innermost-chord drainage lemma, which the same lab finds to
hold on every census web.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.ClosedWebSectorNestingWitness

/-! ## The specimen -/

/-- Tangle edges of the C30 two-hole tangle, indexed `0..34`. -/
def tedges : List (Nat × Nat) :=
  [(0, 10), (1, 11), (2, 13), (3, 15), (4, 17), (5, 22), (6, 29), (7, 24),
   (8, 26), (9, 28), (10, 12), (10, 14), (11, 12), (11, 19), (12, 20),
   (13, 14), (13, 16), (14, 23), (15, 16), (15, 18), (16, 25), (17, 18),
   (17, 19), (18, 27), (19, 21), (20, 22), (20, 24), (21, 22), (21, 29),
   (23, 24), (23, 26), (25, 26), (25, 28), (27, 28), (27, 29)]

/-- The closed-web colouring (colour of edge `i`). -/
def color : List Nat :=
  [0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 2, 2, 1, 0, 1, 2, 0, 0, 2, 1, 0, 2, 1,
   0, 2, 1, 1, 2, 2, 1, 2, 0, 2, 0]

/-- The distinguished colour `a`. -/
def aColor : Nat := 0

/-- Inner-hole and outer-hole spoke edges, and the pendant vertices. -/
def innerSpokes : List Nat := [5, 6, 9, 8, 7]
def outerSpokes : List Nat := [0, 1, 4, 3, 2]
def innerCap : List Nat := [5, 6, 9, 8, 7]
def outerCap : List Nat := [0, 1, 4, 3, 2]

/-- The two rails (vertex sequences), pendant to pendant. -/
def rail0 : List Nat := [3, 15, 18, 27, 28, 9]
def rail1 : List Nat :=
  [4, 17, 19, 11, 12, 10, 14, 13, 16, 25, 26, 23, 24, 20, 22, 21, 29, 6]

/-- The fifteen annulus faces, each as its list of tangle edge ids. -/
def faces : List (List Nat) :=
  [[1, 12, 10, 0], [2, 15, 11, 0], [3, 18, 16, 2], [4, 21, 19, 3],
   [1, 13, 22, 4], [13, 24, 27, 25, 14, 12], [10, 14, 26, 29, 17, 11],
   [16, 20, 31, 30, 17, 15], [18, 20, 32, 33, 23, 19],
   [21, 23, 34, 28, 24, 22], [5, 27, 28, 6], [5, 25, 26, 7],
   [8, 30, 29, 7], [9, 32, 31, 8], [9, 33, 34, 6]]

/-- The claimed sector label of each face. -/
def sectorLabel : List Nat := [0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1]

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
def strands01 : List (List Nat) :=
  [[0, 7, 10, 14, 26], [1, 5, 13, 24, 27], [2, 8, 15, 17, 30],
   [3, 9, 18, 20, 32], [4, 6, 21, 23, 34]]
def strands02 : List (List Nat) :=
  [[0, 7, 11, 17, 29], [1, 5, 12, 14, 25],
   [2, 8, 16, 18, 19, 21, 22, 24, 28, 31, 32, 33, 34]]
def strands12 : List (List Nat) :=
  [[3, 9, 19, 23, 33],
   [4, 6, 10, 11, 12, 13, 15, 16, 20, 22, 25, 26, 27, 28, 29, 30, 31]]

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

/-! ## The kernel-checked facts -/

theorem isProper_true : isProper = true := by decide

theorem strandsValid_true : strandsValid = true := by decide

theorem totallyClosed_true : totallyClosed = true := by decide

theorem rails_true :
    (isRailPath rail0 && isRailPath rail1 && railsCover) = true := by decide

theorem sectors_true :
    (labelsRespectRails && labelClassesConnected) = true := by decide

/-- The three chords are nested on rail 1 and all lie in one sector. -/
theorem nested_same_sector :
    (isRail1Chord 24 && isRail1Chord 14 && isRail1Chord 17 &&
      chordLo 24 < chordLo 14 && chordHi 14 < chordHi 24 &&
      chordLo 14 < chordLo 17 && chordHi 17 < chordHi 14 &&
      chordFacesSameSector 24 && chordFacesSameSector 14 &&
      chordFacesSameSector 17 &&
      chordSector 24 == chordSector 14 && chordSector 14 == chordSector 17)
      = true := by decide

/-- **Universal drainage fails**: chord `(12,20)` (edge 14) does not
drain — its interior vertex `14` sends its `α`-edge `(14,23)` (edge 17)
inside the disk, in the same sector. -/
theorem universalDrainage_false : universalDrainage = false := by decide

theorem chord14_not_drains : chordDrains 14 = false := by decide

end Mettapedia.GraphTheory.ClosedWebSectorNestingWitness
