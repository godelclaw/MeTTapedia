import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularExcess

/-!
# Face tracing for the v24 closed-web sectors

The embedded part of the source's Sector-Alternation lemma is a finite
face-reachability statement.  A same-path chord together with the path
subarc between its endpoints is a primal wall.  Faces remain adjacent after
cutting along that wall exactly when they share some non-wall edge.  The
candidate disk on a chosen side of the chord is hole-free when its component
in this cut facial dual contains neither distinguished hole face.

This module formalizes that checkable obligation.  It deliberately does not
assert that every same-path chord passes the check, nor that hole-freeness by
itself excludes nested chords.  Those are the mathematical content of the
Sector-Alternation step, not cellulation data.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebFaceTracing

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraph
open SimpleGraphDartRotation

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

/-- The facial dual after crossings through the listed primal wall edges have
been removed.  The definition retains an adjacency whenever the two faces
share at least one non-wall edge; it therefore remains exact even before a
unique-shared-edge hypothesis is available. -/
def faceAdjacencyAvoiding
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) : SimpleGraph (AmbientFace allFaces) where
  Adj first second := first.1 ≠ second.1 ∧
    ∃ edge,
      edge ∈ interiorEdgeSupport faceBoundary allFaces ∧
      edge ∉ wall ∧
      edge ∈ faceBoundary first.1 ∧
      edge ∈ faceBoundary second.1
  symm := ⟨by
    rintro first second ⟨hne, edge, hinterior, haway, hfirst, hsecond⟩
    exact ⟨hne.symm, edge, hinterior, haway, hsecond, hfirst⟩⟩
  loopless := ⟨by
    intro face hface
    exact hface.1 rfl⟩

instance instDecidableRelFaceAdjacencyAvoiding
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) :
    DecidableRel (faceAdjacencyAvoiding faceBoundary allFaces wall).Adj := by
  intro first second
  change Decidable (first.1 ≠ second.1 ∧
    ∃ edge,
      edge ∈ interiorEdgeSupport faceBoundary allFaces ∧
      edge ∉ wall ∧
      edge ∈ faceBoundary first.1 ∧
      edge ∈ faceBoundary second.1)
  infer_instance

omit [Fintype F] [DecidableEq F] [Fintype E] in
@[simp] theorem faceAdjacencyAvoiding_adj_iff
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) {first second : AmbientFace allFaces} :
    (faceAdjacencyAvoiding faceBoundary allFaces wall).Adj first second ↔
      first.1 ≠ second.1 ∧
      ∃ edge,
        edge ∈ interiorEdgeSupport faceBoundary allFaces ∧
        edge ∉ wall ∧
        edge ∈ faceBoundary first.1 ∧
        edge ∈ faceBoundary second.1 :=
  Iff.rfl

omit [Fintype F] [DecidableEq F] [Fintype E] in
/-- Cutting primal edges only removes adjacencies from the ordinary facial
dual. -/
theorem faceAdjacencyAvoiding_le_interiorDualGraph
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) :
    faceAdjacencyAvoiding faceBoundary allFaces wall ≤
      interiorDualGraph faceBoundary allFaces := by
  intro first second hadj
  rcases hadj with ⟨hne, edge, hinterior, _haway, hfirst, hsecond⟩
  exact ⟨hne, edge, hinterior, hfirst, hsecond⟩

omit [Fintype F] [DecidableEq F] [Fintype E] in
/-- Enlarging the primal wall can only shrink the cut facial dual. -/
theorem faceAdjacencyAvoiding_anti
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {smallWall largeWall : Finset E} (hwall : smallWall ⊆ largeWall) :
    faceAdjacencyAvoiding faceBoundary allFaces largeWall ≤
      faceAdjacencyAvoiding faceBoundary allFaces smallWall := by
  intro first second hadj
  rcases hadj with ⟨hne, edge, hinterior, hlarge, hfirst, hsecond⟩
  exact ⟨hne, edge, hinterior, fun hsmall => hlarge (hwall hsmall),
    hfirst, hsecond⟩

/-- A selected cut-dual component contains no face from `holes`.  This is the
finite face-tracing formulation of "the bounded region contains no hole
face" used by playbook flag L8. -/
def HoleFreeFaceRegion
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) (seed : AmbientFace allFaces)
    (holes : Finset (AmbientFace allFaces)) : Prop :=
  ∀ hole ∈ holes,
    ¬ (faceAdjacencyAvoiding faceBoundary allFaces wall).Reachable seed hole

instance instDecidableHoleFreeFaceRegion
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) (seed : AmbientFace allFaces)
    (holes : Finset (AmbientFace allFaces)) :
    Decidable (HoleFreeFaceRegion faceBoundary allFaces wall seed holes) := by
  unfold HoleFreeFaceRegion
  infer_instance

omit [Fintype F] [Fintype E] in
/-- A successful finite decision is a kernel-checkable hole-free-region
certificate.  Concrete rotation tables may use this theorem after reducing
the decision, without introducing a separate trusted search procedure. -/
theorem holeFreeFaceRegion_of_decide_eq_true
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) (seed : AmbientFace allFaces)
    (holes : Finset (AmbientFace allFaces))
    (hcheck : decide
      (HoleFreeFaceRegion faceBoundary allFaces wall seed holes) = true) :
    HoleFreeFaceRegion faceBoundary allFaces wall seed holes := by
  exact of_decide_eq_true hcheck

section NoncrossingAudit

/-- A chord on a linearly ordered path, represented by its ordered endpoint
positions. -/
structure OrderedPathChord (length : Nat) where
  left : Fin length
  right : Fin length
  left_lt_right : left < right
  deriving DecidableEq

/-- Ordered chords are the finite subtype of ordered pairs of path
positions. -/
def orderedPathChordEquiv (length : Nat) :
    OrderedPathChord length ≃
      {pair : Fin length × Fin length // pair.1 < pair.2} where
  toFun chord := ⟨(chord.left, chord.right), chord.left_lt_right⟩
  invFun pair := ⟨pair.1.1, pair.1.2, pair.2⟩
  left_inv chord := by cases chord; rfl
  right_inv pair := by cases pair; rfl

instance instFintypeOrderedPathChord (length : Nat) :
    Fintype (OrderedPathChord length) :=
  Fintype.ofEquiv
    {pair : Fin length × Fin length // pair.1 < pair.2}
    (orderedPathChordEquiv length).symm

/-- Two path chords cross when their endpoints strictly interleave.  Nested
endpoint intervals are deliberately not crossings. -/
def OrderedPathChord.Crosses {length : Nat}
    (first second : OrderedPathChord length) : Prop :=
  (first.left < second.left ∧ second.left < first.right ∧
      first.right < second.right) ∨
    (second.left < first.left ∧ first.left < second.right ∧
      second.right < first.right)

instance {length : Nat} (first second : OrderedPathChord length) :
    Decidable (first.Crosses second) := by
  unfold OrderedPathChord.Crosses
  infer_instance

/-- The first chord lies strictly inside the endpoint interval of the
second. -/
def OrderedPathChord.NestedIn {length : Nat}
    (inner outer : OrderedPathChord length) : Prop :=
  outer.left < inner.left ∧ inner.right < outer.right

instance {length : Nat} (inner outer : OrderedPathChord length) :
    Decidable (inner.NestedIn outer) := by
  unfold OrderedPathChord.NestedIn
  infer_instance

/-- A finite chord diagram is noncrossing when distinct members never have
strictly interleaving endpoints. -/
def PairwiseNoncrossing {length : Nat}
    (chords : Finset (OrderedPathChord length)) : Prop :=
  ∀ first ∈ chords, ∀ second ∈ chords,
    first ≠ second → ¬ first.Crosses second

instance {length : Nat} (chords : Finset (OrderedPathChord length)) :
    Decidable (PairwiseNoncrossing chords) := by
  unfold PairwiseNoncrossing
  infer_instance

/-- Distinct chords of a matching share no path endpoint. -/
def PairwiseEndpointDisjoint {length : Nat}
    (chords : Finset (OrderedPathChord length)) : Prop :=
  ∀ first ∈ chords, ∀ second ∈ chords,
    first ≠ second →
      first.left ≠ second.left ∧
      first.left ≠ second.right ∧
      first.right ≠ second.left ∧
      first.right ≠ second.right

/-- No distinct chord lies strictly inside `outer`. -/
def InnermostIn {length : Nat} (outer : OrderedPathChord length)
    (chords : Finset (OrderedPathChord length)) : Prop :=
  ∀ inner ∈ chords, inner ≠ outer → ¬ inner.NestedIn outer

/-- A chord has an endpoint on the open subarc cut off by `outer`. -/
def OrderedPathChord.HasEndpointInside {length : Nat}
    (chord outer : OrderedPathChord length) : Prop :=
  (outer.left < chord.left ∧ chord.left < outer.right) ∨
    (outer.left < chord.right ∧ chord.right < outer.right)

/-- The corrected elementary drainage step: for an innermost chord in a
noncrossing matching, no other same-path chord can touch the open subarc.
Without `InnermostIn` the statement is false by the witness below. -/
theorem not_hasEndpointInside_of_innermost_of_pairwiseNoncrossing
    {length : Nat} {chords : Finset (OrderedPathChord length)}
    {outer chord : OrderedPathChord length}
    (hnoncrossing : PairwiseNoncrossing chords)
    (hdisjoint : PairwiseEndpointDisjoint chords)
    (hinnermost : InnermostIn outer chords)
    (houter : outer ∈ chords) (hchord : chord ∈ chords)
    (hne : chord ≠ outer) :
    ¬ chord.HasEndpointInside outer := by
  have hnotCrosses : ¬ outer.Crosses chord :=
    hnoncrossing outer houter chord hchord hne.symm
  have hendpoints := hdisjoint outer houter chord hchord hne.symm
  have hnotNested : ¬ chord.NestedIn outer :=
    hinnermost chord hchord hne
  unfold OrderedPathChord.Crosses at hnotCrosses
  unfold OrderedPathChord.NestedIn at hnotNested
  unfold OrderedPathChord.HasEndpointInside
  omega

private def nestedOuterChord : OrderedPathChord 10 :=
  ⟨0, 9, by decide⟩

private def nestedInnerChord : OrderedPathChord 10 :=
  ⟨2, 7, by decide⟩

private def nestedNoncrossingDiagram : Finset (OrderedPathChord 10) :=
  {nestedOuterChord, nestedInnerChord}

/-- Noncrossing alone does not exclude a same-path nested chord.  This small
regression witness isolates the extra premise still needed in the prose
Sector-Alternation argument; it does not claim that the witness satisfies the
other closed-web hypotheses. -/
theorem exists_nested_pairwiseNoncrossing_path_chords :
    ∃ (chords : Finset (OrderedPathChord 10))
        (outer inner : OrderedPathChord 10),
      PairwiseNoncrossing chords ∧
      outer ∈ chords ∧ inner ∈ chords ∧
      inner.NestedIn outer := by
  exact ⟨nestedNoncrossingDiagram, nestedOuterChord, nestedInnerChord, by decide⟩

end NoncrossingAudit

section WalkWall

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The graph-edge subtype carried by the edges of a walk. -/
noncomputable def walkEdgeFinset {start finish : V}
    (walk : G.Walk start finish) : Finset G.edgeSet :=
  Finset.univ.filter fun edge : G.edgeSet => edge.1 ∈ walk.edges

@[simp] theorem mem_walkEdgeFinset_iff {start finish : V}
    (walk : G.Walk start finish) (edge : G.edgeSet) :
    edge ∈ walkEdgeFinset walk ↔ edge.1 ∈ walk.edges := by
  classical
  simp [walkEdgeFinset]

/-- A chord and the simple path subarc joining its endpoints.  The chord is
required not to be one of the subarc edges, so their union is the intended
simple closed primal wall. -/
structure SamePathChordBoundary (G : SimpleGraph V) where
  chord : G.Dart
  subarc : G.Walk chord.fst chord.snd
  subarc_isPath : subarc.IsPath
  chord_not_mem_subarc : chord.edge ∉ subarc.edges

namespace SamePathChordBoundary

/-- The chord as an edge of the ambient graph. -/
def chordEdge (boundary : SamePathChordBoundary G) : G.edgeSet :=
  ⟨boundary.chord.edge, boundary.chord.edge_mem⟩

/-- The primal wall used by the L8 face trace. -/
noncomputable def wall (boundary : SamePathChordBoundary G) : Finset G.edgeSet :=
  insert boundary.chordEdge (walkEdgeFinset boundary.subarc)

@[simp] theorem chordEdge_mem_wall
    (boundary : SamePathChordBoundary G) :
    boundary.chordEdge ∈ boundary.wall := by
  classical
  simp [wall]

@[simp] theorem mem_wall_iff
    (boundary : SamePathChordBoundary G) (edge : G.edgeSet) :
    edge ∈ boundary.wall ↔
      edge = boundary.chordEdge ∨ edge.1 ∈ boundary.subarc.edges := by
  classical
  simp [wall, mem_walkEdgeFinset_iff]

end SamePathChordBoundary

section AnnularCellulation

noncomputable section

variable (cell : FramedAnnularCellulation G)

abbrev CellRS := cell.rotation.toRotationSystem

/-- All orbit faces as vertices of the full facial dual. -/
abbrev FullFace := AmbientFace
  (Finset.univ : Finset (OrbitFace (CellRS cell)))

/-- A distinguished orbit face as a vertex of the full facial dual. -/
noncomputable def fullFace (face : OrbitFace (CellRS cell)) : FullFace cell :=
  ⟨face, Finset.mem_univ face⟩

/-- The two source hole faces in the full facial dual. -/
noncomputable def holeFullFaces : Finset (FullFace cell) :=
  {fullFace cell cell.innerHole, fullFace cell cell.outerHole}

/-- The two facial sides of the chord edge, selected by its orientation.
`false` chooses the face containing the chord dart and `true` the face
containing its flipped dart. -/
noncomputable def chordSideFace
    (boundary : SamePathChordBoundary G) (side : Bool) :
    OrbitFace (CellRS cell) :=
  if side then
    dartOrbitFace (CellRS cell) ((CellRS cell).alpha boundary.chord)
  else dartOrbitFace (CellRS cell) boundary.chord

/-- The exact L8 face-tracing obligation for one chosen side of a
chord-plus-subarc wall. -/
noncomputable def HoleFreeChordSide
    (boundary : SamePathChordBoundary G) (side : Bool) : Prop :=
  HoleFreeFaceRegion
    (orbitFaceBoundary (CellRS cell))
    (Finset.univ : Finset (OrbitFace (CellRS cell)))
    boundary.wall
    (fullFace cell (chordSideFace cell boundary side))
    (holeFullFaces cell)

/-- Unfold the annular L8 obligation into the two explicit non-reachability
checks. -/
theorem holeFreeChordSide_iff
    (boundary : SamePathChordBoundary G) (side : Bool) :
    HoleFreeChordSide cell boundary side ↔
      ¬ (faceAdjacencyAvoiding
        (orbitFaceBoundary (CellRS cell))
        (Finset.univ : Finset (OrbitFace (CellRS cell)))
        boundary.wall).Reachable
          (fullFace cell (chordSideFace cell boundary side))
          (fullFace cell cell.innerHole) ∧
      ¬ (faceAdjacencyAvoiding
        (orbitFaceBoundary (CellRS cell))
        (Finset.univ : Finset (OrbitFace (CellRS cell)))
        boundary.wall).Reachable
          (fullFace cell (chordSideFace cell boundary side))
          (fullFace cell cell.outerHole) := by
  classical
  simp [HoleFreeChordSide, HoleFreeFaceRegion, holeFullFaces]

end

end AnnularCellulation

end WalkWall

end GoertzelV24ClosedWebFaceTracing

end Mettapedia.GraphTheory.FourColor
