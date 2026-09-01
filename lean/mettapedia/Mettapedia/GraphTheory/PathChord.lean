import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Intervals and chords of graph walks

This file contains graph-theoretic syntax for intervals of walks and chords
whose endpoints occur on one walk.  It is independent of embeddings,
colourings, and the four-colour development.

An `OrderedPathChord` records only two ordered coordinates.  A
`SamePathChordBoundary` additionally records the ambient chord dart and the
simple walk interval joining its endpoints; its wall is the union of that
dart's edge and the interval edges.
-/

namespace Mettapedia.GraphTheory

open SimpleGraph

universe u

/-! ## Walk intervals -/

/-- The oriented interval of a walk between two ordered vertex positions. -/
def walkInterval {V : Type u} {G : SimpleGraph V} {start finish : V}
    (walk : G.Walk start finish) (left right : Nat) (horder : left ≤ right) :
    G.Walk (walk.getVert left) (walk.getVert right) :=
  ((walk.drop left).take (right - left)).copy rfl (by
    simp [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le horder])

/-- Taking an interval of a path again gives a path. -/
theorem walkInterval_isPath {V : Type u} {G : SimpleGraph V}
    {start finish : V} {walk : G.Walk start finish} (hwalk : walk.IsPath)
    (left right : Nat) (horder : left ≤ right) :
    (walkInterval walk left right horder).IsPath := by
  simpa [walkInterval] using (hwalk.drop left).take (right - left)

/-- Within the range of the original walk, an interval has the expected
number of edges. -/
theorem walkInterval_length {V : Type u} {G : SimpleGraph V}
    {start finish : V} (walk : G.Walk start finish) (left right : Nat)
    (horder : left ≤ right) (hright : right ≤ walk.length) :
    (walkInterval walk left right horder).length = right - left := by
  simp only [walkInterval, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
  rw [Nat.min_eq_left]
  omega

/-- Vertex lookup inside a bounded walk interval is lookup at the translated
position in the original walk. -/
theorem walkInterval_getVert {V : Type u} {G : SimpleGraph V}
    {start finish : V} (walk : G.Walk start finish)
    (left right position : Nat) (horder : left ≤ right)
    (hposition : position ≤ right - left) :
    (walkInterval walk left right horder).getVert position =
      walk.getVert (left + position) := by
  simp [walkInterval, SimpleGraph.Walk.take_getVert,
    SimpleGraph.Walk.drop_getVert, Nat.min_eq_right hposition]

/-! ## Ordered chord coordinates -/

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

/-- For an innermost chord in a noncrossing endpoint-disjoint family, no
other chord can touch its open subarc. -/
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

/-- Noncrossing alone does not exclude a nested chord. -/
theorem exists_nested_pairwiseNoncrossing_path_chords :
    ∃ (chords : Finset (OrderedPathChord 10))
        (outer inner : OrderedPathChord 10),
      PairwiseNoncrossing chords ∧
      outer ∈ chords ∧ inner ∈ chords ∧
      inner.NestedIn outer := by
  exact ⟨nestedNoncrossingDiagram, nestedOuterChord, nestedInnerChord, by decide⟩

/-! ## Chord boundaries in a graph -/

variable {V : Type u} [Fintype V] [DecidableEq V]
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
required not to be one of the subarc edges. -/
structure SamePathChordBoundary (G : SimpleGraph V) where
  chord : G.Dart
  subarc : G.Walk chord.fst chord.snd
  subarc_isPath : subarc.IsPath
  chord_not_mem_subarc : chord.edge ∉ subarc.edges

namespace SamePathChordBoundary

/-- The chord as an edge of the ambient graph. -/
def chordEdge (boundary : SamePathChordBoundary G) : G.edgeSet :=
  ⟨boundary.chord.edge, boundary.chord.edge_mem⟩

/-- The chord together with its path interval. -/
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

/-- Traverse the chord and return along its path interval. -/
def cycleWalk (boundary : SamePathChordBoundary G) :
    G.Walk boundary.chord.fst boundary.chord.fst :=
  boundary.subarc.reverse.cons boundary.chord.adj

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A chord and its simple path interval form a simple cycle. -/
theorem cycleWalk_isCycle (boundary : SamePathChordBoundary G) :
    boundary.cycleWalk.IsCycle := by
  rw [cycleWalk, SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨boundary.subarc_isPath.reverse, ?_⟩
  simpa [SimpleGraph.Dart.edge] using boundary.chord_not_mem_subarc

/-- The generic wall contains exactly the edges of the chord cycle. -/
theorem mem_wall_iff_mem_cycleWalk_edges
    (boundary : SamePathChordBoundary G) (edge : G.edgeSet) :
    edge ∈ boundary.wall ↔ edge.1 ∈ boundary.cycleWalk.edges := by
  classical
  simp [cycleWalk, SamePathChordBoundary.mem_wall_iff, chordEdge,
    SimpleGraph.Dart.edge, Subtype.ext_iff]

end SamePathChordBoundary

end Mettapedia.GraphTheory
