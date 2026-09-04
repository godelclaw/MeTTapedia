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

/-- The dart list of a walk interval is the corresponding slice of the
ambient walk's dart list. -/
theorem walkInterval_darts {V : Type u} {G : SimpleGraph V}
    {start finish : V} (walk : G.Walk start finish)
    (left right : Nat) (horder : left ≤ right) :
    (walkInterval walk left right horder).darts =
      (walk.darts.drop left).take (right - left) := by
  simp [walkInterval, SimpleGraph.Walk.darts_take,
    SimpleGraph.Walk.darts_drop]

/-- A dart in a bounded walk prefix is based at an original walk coordinate
strictly below the bound. -/
theorem exists_coordinate_lt_of_mem_darts_take
    {V : Type u} {G : SimpleGraph V} {start finish : V}
    (walk : G.Walk start finish) (bound : Nat)
    (hbound : bound ≤ walk.length) (dart : G.Dart)
    (hdart : dart ∈ (walk.take bound).darts) :
    ∃ coordinate : Nat, coordinate < bound ∧
      dart.fst = walk.getVert coordinate := by
  rcases List.mem_iff_getElem.mp hdart with ⟨coordinate, hcoordinate, rfl⟩
  have hcoordinateBound : coordinate < bound := by
    simpa [SimpleGraph.Walk.length_darts,
      SimpleGraph.Walk.take_length, Nat.min_eq_left hbound] using hcoordinate
  refine ⟨coordinate, hcoordinateBound, ?_⟩
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
  simp [SimpleGraph.Walk.take_getVert,
    Nat.min_eq_right (Nat.le_of_lt hcoordinateBound)]

/-- Taking a positive bounded prefix preserves the first oriented dart. -/
theorem firstDart_take_eq
    {V : Type u} {G : SimpleGraph V} {start finish : V}
    (walk : G.Walk start finish) (bound : Nat)
    (hpositive : 0 < bound) (hbound : bound ≤ walk.length) :
    (walk.take bound).firstDart (by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        simp [SimpleGraph.Walk.take_length, Nat.min_eq_left hbound,
          hpositive]) =
      walk.firstDart (by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        exact lt_of_lt_of_le hpositive hbound) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · simp [SimpleGraph.Walk.firstDart,
      SimpleGraph.Walk.take_getVert,
      Nat.min_eq_right (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hpositive))]

/-- A dart in a dropped walk suffix is based at an original coordinate at
or after the drop point and strictly before the original finish. -/
theorem exists_coordinate_ge_of_mem_darts_drop
    {V : Type u} {G : SimpleGraph V} {start finish : V}
    (walk : G.Walk start finish) (bound : Nat)
    (hbound : bound ≤ walk.length) (dart : G.Dart)
    (hdart : dart ∈ (walk.drop bound).darts) :
    ∃ coordinate : Nat, bound ≤ coordinate ∧
      coordinate < walk.length ∧ dart.fst = walk.getVert coordinate := by
  rcases List.mem_iff_getElem.mp hdart with ⟨offset, hoffset, rfl⟩
  have hoffsetBound : offset < walk.length - bound := by
    simpa [SimpleGraph.Walk.length_darts,
      SimpleGraph.Walk.drop_length] using hoffset
  refine ⟨bound + offset, Nat.le_add_right _ _, by omega, ?_⟩
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
  simp [SimpleGraph.Walk.drop_getVert]

/-- Dropping a proper prefix preserves the final oriented dart. -/
theorem lastDart_drop_eq
    {V : Type u} {G : SimpleGraph V} {start finish : V}
    (walk : G.Walk start finish) (bound : Nat)
    (hbound : bound < walk.length) :
    (walk.drop bound).lastDart (by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length,
          SimpleGraph.Walk.drop_length]
        omega) =
      walk.lastDart (by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        omega) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · change (walk.drop bound).penultimate = walk.penultimate
    simp only [SimpleGraph.Walk.penultimate,
      SimpleGraph.Walk.drop_length,
      SimpleGraph.Walk.drop_getVert]
    congr 1
    omega
  · rfl

/-! ## Paths as arcs of simple cycles -/

/-- A nonempty walk together with a nonempty complementary walk whose
concatenation is a simple cycle.  This is the intrinsic graph-theoretic
statement that the distinguished walk is one oriented arc of that cycle. -/
structure PathCycleClosure {V : Type u} {G : SimpleGraph V}
    {start finish : V} (path : G.Walk start finish) where
  complement : G.Walk finish start
  path_not_nil : ¬ path.Nil
  complement_not_nil : ¬ complement.Nil
  cycle_isCycle : (path.append complement).IsCycle

namespace PathCycleClosure

variable {V : Type u} {G : SimpleGraph V} {start finish : V}
  {path : G.Walk start finish}

/-- The distinguished arc of a simple-cycle closure is a simple path. -/
theorem path_isPath (closure : PathCycleClosure path) : path.IsPath :=
  closure.cycle_isCycle.isPath_of_append_left closure.complement_not_nil

/-- The complementary arc of a simple-cycle closure is a simple path. -/
theorem complement_isPath (closure : PathCycleClosure path) :
    closure.complement.IsPath :=
  closure.cycle_isCycle.isPath_of_append_right closure.path_not_nil

/-- Apart from their common endpoints, the two arcs of a simple-cycle
closure have disjoint vertex supports. -/
theorem tail_support_disjoint (closure : PathCycleClosure path) :
    path.support.tail.Disjoint closure.complement.support.tail := by
  have hnodup := closure.cycle_isCycle.2
  rw [SimpleGraph.Walk.tail_support_append, List.nodup_append'] at hnodup
  exact hnodup.2.2

/-- The two arcs of a simple-cycle closure have disjoint edge lists. -/
theorem edges_disjoint (closure : PathCycleClosure path) :
    path.edges.Disjoint closure.complement.edges := by
  have hnodup := closure.cycle_isCycle.isTrail.edges_nodup
  rw [SimpleGraph.Walk.edges_append, List.nodup_append'] at hnodup
  exact hnodup.2.2

/-- The arc of the closing cycle that runs from a later path coordinate back
to an earlier one without traversing the intervening path interval.  It is
the path suffix, followed by the stored complementary arc, followed by the
path prefix. -/
noncomputable def exteriorInterval (closure : PathCycleClosure path)
    (left right : Fin (path.length + 1)) :
    G.Walk (path.getVert right) (path.getVert left) := by
  have hleft : left.val ≤ path.length := Nat.lt_succ_iff.mp left.isLt
  have hright : right.val ≤ path.length := Nat.lt_succ_iff.mp right.isLt
  let suffix : G.Walk (path.getVert right) finish :=
    (path.drop right).copy (by simp [Nat.min_eq_left hright]) rfl
  let initialArc : G.Walk start (path.getVert left) :=
    (path.take left).copy rfl (by simp [Nat.min_eq_left hleft])
  exact suffix.append (closure.complement.append initialArc)

/-- The exterior interval has the expected three-piece dart list. -/
theorem exteriorInterval_darts (closure : PathCycleClosure path)
    (left right : Fin (path.length + 1)) :
    (closure.exteriorInterval left right).darts =
      path.darts.drop right ++ (closure.complement.darts ++
        path.darts.take left) := by
  simp [exteriorInterval, SimpleGraph.Walk.darts_append,
    SimpleGraph.Walk.darts_drop, SimpleGraph.Walk.darts_take]

/-- An exterior interval from a strictly later coordinate to a strictly
earlier one is nonempty. -/
theorem exteriorInterval_not_nil (closure : PathCycleClosure path)
    (hpath : path.IsPath) (left right : Fin (path.length + 1))
    (horder : left < right) :
    ¬(closure.exteriorInterval left right).Nil := by
  apply SimpleGraph.Walk.not_nil_of_ne
  intro hvertices
  have hcoordinates := hpath.getVert_injOn
    (Nat.lt_succ_iff.mp right.isLt) (Nat.lt_succ_iff.mp left.isLt) hvertices
  omega

/-- Every based dart of the exterior interval either occurs at a path
coordinate outside the open interval from `left` to `right`, or is based in
the interior of the stored complementary arc. -/
theorem based_vertex_of_mem_exteriorInterval_darts
    (closure : PathCycleClosure path)
    (left right : Fin (path.length + 1)) (dart : G.Dart)
    (hdart : dart ∈ (closure.exteriorInterval left right).darts) :
    (∃ coordinate : Nat,
        (coordinate < left.val ∨ right.val ≤ coordinate) ∧
          coordinate ≤ path.length ∧
          dart.fst = path.getVert coordinate) ∨
      dart.fst ∈ closure.complement.support.tail := by
  rw [closure.exteriorInterval_darts] at hdart
  rcases List.mem_append.mp hdart with hsuffix | hrest
  · have hright : right.val ≤ path.length := Nat.lt_succ_iff.mp right.isLt
    have hsuffix' : dart ∈ (path.drop right).darts := by
      simpa [SimpleGraph.Walk.darts_drop] using hsuffix
    rcases exists_coordinate_ge_of_mem_darts_drop path right hright dart
        hsuffix' with ⟨coordinate, hcoordinate, hbound, hbase⟩
    exact Or.inl ⟨coordinate, Or.inr hcoordinate,
      Nat.le_of_lt hbound, hbase⟩
  · rcases List.mem_append.mp hrest with hcomplement | hinitial
    · have hsupport : dart.fst ∈ closure.complement.support :=
        closure.complement.dart_fst_mem_support_of_mem_darts hcomplement
      rw [closure.complement.mem_support_iff] at hsupport
      rcases hsupport with hfinish | hinterior
      · left
        refine ⟨path.length, Or.inr (Nat.lt_succ_iff.mp right.isLt),
          le_rfl, ?_⟩
        simpa [hfinish]
      · exact Or.inr hinterior
    · have hleft : left.val ≤ path.length := Nat.lt_succ_iff.mp left.isLt
      have hinitial' : dart ∈ (path.take left).darts := by
        simpa [SimpleGraph.Walk.darts_take] using hinitial
      rcases exists_coordinate_lt_of_mem_darts_take path left hleft dart
          hinitial' with ⟨coordinate, hcoordinate, hbase⟩
      exact Or.inl ⟨coordinate, Or.inl hcoordinate,
        Nat.le_trans (Nat.le_of_lt hcoordinate) hleft, hbase⟩

end PathCycleClosure

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

/-- The two endpoint coordinates of one ordered chord. -/
def OrderedPathChord.endpointFinset {length : Nat}
    (chord : OrderedPathChord length) : Finset (Fin length) :=
  {chord.left, chord.right}

@[simp] theorem OrderedPathChord.card_endpointFinset
    {length : Nat} (chord : OrderedPathChord length) :
    chord.endpointFinset.card = 2 := by
  simp [OrderedPathChord.endpointFinset, ne_of_lt chord.left_lt_right]

/-- All endpoint coordinates used by a finite chord family. -/
def orderedPathChordEndpoints {length : Nat}
    (chords : Finset (OrderedPathChord length)) : Finset (Fin length) :=
  chords.biUnion OrderedPathChord.endpointFinset

@[simp] theorem mem_orderedPathChordEndpoints_iff
    {length : Nat} {chords : Finset (OrderedPathChord length)}
    {coordinate : Fin length} :
    coordinate ∈ orderedPathChordEndpoints chords ↔
      ∃ chord ∈ chords,
        coordinate = chord.left ∨ coordinate = chord.right := by
  simp [orderedPathChordEndpoints, OrderedPathChord.endpointFinset]

/-- A chord family uses at most two endpoint coordinates per chord.  No
disjointness hypothesis is needed for this upper bound. -/
theorem card_orderedPathChordEndpoints_le_two_mul
    {length : Nat} (chords : Finset (OrderedPathChord length)) :
    (orderedPathChordEndpoints chords).card ≤ 2 * chords.card := by
  calc
    (orderedPathChordEndpoints chords).card ≤
        ∑ chord ∈ chords, chord.endpointFinset.card := by
      exact Finset.card_biUnion_le
    _ = 2 * chords.card := by simp [Nat.mul_comm]

/-- A chord crossing `outer` is open at the sweep cut through one of
`outer`'s two endpoints. -/
theorem OrderedPathChord.open_at_left_or_right_of_crosses
    {length : Nat} {chord outer : OrderedPathChord length}
    (hcrosses : chord.Crosses outer) :
    (chord.left < outer.left ∧ outer.left ≤ chord.right) ∨
      (chord.left < outer.right ∧ outer.right ≤ chord.right) := by
  unfold OrderedPathChord.Crosses at hcrosses
  rcases hcrosses with hleft | hright
  · exact Or.inl ⟨hleft.1, hleft.2.1.le⟩
  · exact Or.inr ⟨hright.2.1, hright.2.2.le⟩

/-- Every nonempty finite chord family has an innermost member.  Choose a
chord of minimum endpoint span; a chord strictly nested inside it would have
strictly smaller span. -/
theorem exists_innermost_orderedPathChord
    {length : Nat} {chords : Finset (OrderedPathChord length)}
    (hnonempty : chords.Nonempty) :
    ∃ chord ∈ chords, InnermostIn chord chords := by
  obtain ⟨chord, hchord, hminimal⟩ :=
    Finset.exists_min_image chords
      (fun candidate => candidate.right.val - candidate.left.val)
      hnonempty
  refine ⟨chord, hchord, ?_⟩
  intro inner hinner _hne hnested
  have hspanStrict :
      inner.right.val - inner.left.val <
        chord.right.val - chord.left.val := by
    unfold OrderedPathChord.NestedIn at hnested
    have hinnerOrder := inner.left_lt_right
    have hchordOrder := chord.left_lt_right
    omega
  exact (Nat.not_lt_of_ge (hminimal inner hinner)) hspanStrict

/-- In an endpoint-disjoint chord family, every distinct chord touching the
open interval of an innermost member crosses that member.  The only other
order type would put the touching chord strictly inside. -/
theorem OrderedPathChord.crosses_of_hasEndpointInside_of_innermost
    {length : Nat} {chords : Finset (OrderedPathChord length)}
    {outer chord : OrderedPathChord length}
    (hdisjoint : PairwiseEndpointDisjoint chords)
    (hinnermost : InnermostIn outer chords)
    (houter : outer ∈ chords) (hchord : chord ∈ chords)
    (hne : chord ≠ outer)
    (htouches : chord.HasEndpointInside outer) :
    chord.Crosses outer := by
  have hendpoints := hdisjoint outer houter chord hchord hne.symm
  have hnotNested : ¬ chord.NestedIn outer :=
    hinnermost chord hchord hne
  unfold OrderedPathChord.HasEndpointInside at htouches
  unfold OrderedPathChord.NestedIn at hnotNested
  unfold OrderedPathChord.Crosses
  have houterOrder := outer.left_lt_right
  have hchordOrder := chord.left_lt_right
  omega

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

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The first dart of the oriented chord cycle is its chord dart. -/
theorem firstDart_cycleWalk (boundary : SamePathChordBoundary G) :
    boundary.cycleWalk.firstDart boundary.cycleWalk_isCycle.not_nil =
      boundary.chord := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · simpa [cycleWalk] using
      SimpleGraph.Walk.snd_cons boundary.subarc.reverse boundary.chord.adj

/-- The generic wall contains exactly the edges of the chord cycle. -/
theorem mem_wall_iff_mem_cycleWalk_edges
    (boundary : SamePathChordBoundary G) (edge : G.edgeSet) :
    edge ∈ boundary.wall ↔ edge.1 ∈ boundary.cycleWalk.edges := by
  classical
  simp [cycleWalk, SamePathChordBoundary.mem_wall_iff, chordEdge,
    SimpleGraph.Dart.edge, Subtype.ext_iff]

end SamePathChordBoundary

end Mettapedia.GraphTheory
