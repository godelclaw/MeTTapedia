import Mettapedia.GraphTheory.CubicPathAttachment
import Mettapedia.GraphTheory.PathChord

/-!
# Chords supplied by cubic path attachments

When the unique third edge at an internal vertex of a simple path returns to
the path, it canonically determines an ordered path chord.  This file packages
that edge together with the intervening path interval as a
`SamePathChordBoundary`.

The construction is graph-theoretic.  It does not assume an embedding or
claim that one of the two sides is a disk.
-/

namespace Mettapedia.GraphTheory.CubicPathAttachment

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {start finish : V}

namespace InternalPosition

/-- An internal position viewed as a coordinate in the full path support. -/
def coordinate {path : G.Walk start finish}
    (position : InternalPosition path) : Fin (path.length + 1) :=
  ⟨position.index, Nat.lt_succ_of_lt position.index_lt_length⟩

@[simp] theorem coordinate_val {path : G.Walk start finish}
    (position : InternalPosition path) :
    position.coordinate.val = position.index :=
  rfl

end InternalPosition

variable [G.LocallyFinite]

namespace ChordAttachment

/-- The two endpoints recorded by a chord attachment are distinct. -/
theorem coordinate_ne_otherPosition
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    position.coordinate ≠ chord.otherPosition := by
  intro heq
  have hvertices : position.vertex =
      attachmentNeighbor hpath hregular position := by
    calc
      position.vertex = path.getVert chord.otherPosition := by
        apply congrArg path.getVert
        exact Fin.ext_iff.mp heq
      _ = attachmentNeighbor hpath hregular position := chord.endpoint_eq
  exact (attachmentNeighbor_adj hpath hregular position).ne hvertices

/-- The ordered coordinate pair underlying a chord attachment. -/
noncomputable def orderedCoordinates
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    OrderedPathChord (path.length + 1) :=
  if horder : position.coordinate < chord.otherPosition then
    ⟨position.coordinate, chord.otherPosition, horder⟩
  else
    ⟨chord.otherPosition, position.coordinate,
      lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt horder))
        (chord.coordinate_ne_otherPosition hpath hregular position).symm⟩

/-- A chord attachment is canonically oriented when the internal position
which produced it is its earlier path endpoint. -/
def IsLeftEndpoint
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) : Prop :=
  position.coordinate =
    (chord.orderedCoordinates hpath hregular position).left

/-- The position producing a chord is one of its two ordered endpoints. -/
theorem coordinate_eq_left_or_right
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    position.coordinate =
        (chord.orderedCoordinates hpath hregular position).left ∨
      position.coordinate =
        (chord.orderedCoordinates hpath hregular position).right := by
  by_cases horder : position.coordinate < chord.otherPosition
  · exact Or.inl (by simp [orderedCoordinates, horder])
  · exact Or.inr (by simp [orderedCoordinates, horder])

/-- For a canonically oriented attachment, the recorded other position is
the later ordered endpoint. -/
theorem otherPosition_eq_right_of_isLeftEndpoint
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position)
    (hleft : chord.IsLeftEndpoint hpath hregular position) :
    chord.otherPosition =
      (chord.orderedCoordinates hpath hregular position).right := by
  by_cases horder : position.coordinate < chord.otherPosition
  · simp [orderedCoordinates, horder]
  · have hne := chord.coordinate_ne_otherPosition hpath hregular position
    simp only [IsLeftEndpoint, orderedCoordinates, horder, dite_false] at hleft
    exact False.elim (hne hleft)

/-- The coordinate span of a cubic attachment chord is at least two path
edges: the attachment edge is not either adjacent path edge. -/
theorem one_lt_orderedCoordinates_span
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    1 < (chord.orderedCoordinates hpath hregular position).right.val -
      (chord.orderedCoordinates hpath hregular position).left.val := by
  by_cases horder : position.coordinate < chord.otherPosition
  · have hnotNext := chord.not_next
    simp only [orderedCoordinates, horder, dite_true,
      InternalPosition.coordinate_val]
    change 1 < chord.otherPosition.val - position.index
    have hlt : position.index < chord.otherPosition.val := horder
    omega
  · have hnotPrevious := chord.not_previous
    have hne := chord.coordinate_ne_otherPosition hpath hregular position
    have hneVal : chord.otherPosition.val ≠ position.index := by
      intro heq
      apply hne
      exact Fin.ext heq.symm
    have hle : chord.otherPosition.val ≤ position.index := by
      simpa [InternalPosition.coordinate] using Nat.le_of_not_gt horder
    simp only [orderedCoordinates, horder, dite_false,
      InternalPosition.coordinate_val]
    change 1 < position.index - chord.otherPosition.val
    omega

/-- The two ordered endpoint vertices of a cubic attachment chord are
adjacent by the attachment edge. -/
theorem getVert_orderedCoordinates_adj
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    G.Adj
      (path.getVert (chord.orderedCoordinates hpath hregular position).left)
      (path.getVert (chord.orderedCoordinates hpath hregular position).right) := by
  by_cases horder : position.coordinate < chord.otherPosition
  · simp only [orderedCoordinates, horder, dite_true]
    change G.Adj (path.getVert position.index)
      (path.getVert chord.otherPosition)
    rw [chord.endpoint_eq]
    exact attachmentNeighbor_adj hpath hregular position
  · simp only [orderedCoordinates, horder, dite_false]
    change G.Adj (path.getVert chord.otherPosition)
      (path.getVert position.index)
    rw [chord.endpoint_eq]
    exact (attachmentNeighbor_adj hpath hregular position).symm

/-- The chord dart oriented from its earlier path coordinate to its later
coordinate. -/
noncomputable def chordDart
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) : G.Dart :=
  ⟨(path.getVert (chord.orderedCoordinates hpath hregular position).left,
      path.getVert (chord.orderedCoordinates hpath hregular position).right),
    chord.getVert_orderedCoordinates_adj hpath hregular position⟩

/-- The path interval between the ordered endpoints of an attachment chord. -/
noncomputable def subarc
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    G.Walk (chord.chordDart hpath hregular position).fst
      (chord.chordDart hpath hregular position).snd :=
  walkInterval path
    (chord.orderedCoordinates hpath hregular position).left
    (chord.orderedCoordinates hpath hregular position).right
    chord.orderedCoordinates.left_lt_right.le

/-- The oriented darts of an attachment chord's subarc are exactly the
corresponding slice of the ambient path. -/
theorem subarc_darts
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    (chord.subarc hpath hregular position).darts =
      (path.darts.drop
        (chord.orderedCoordinates hpath hregular position).left).take
        ((chord.orderedCoordinates hpath hregular position).right -
          (chord.orderedCoordinates hpath hregular position).left) := by
  simp [subarc, chordDart, walkInterval,
    SimpleGraph.Walk.darts_take, SimpleGraph.Walk.darts_drop]

/-- The attachment chord's path interval remains simple. -/
theorem subarc_isPath
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    (chord.subarc hpath hregular position).IsPath :=
  walkInterval_isPath hpath _ _ chord.orderedCoordinates.left_lt_right.le

/-- The attachment chord edge is not an edge of its intervening path
interval. -/
theorem chord_not_mem_subarc
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    (chord.chordDart hpath hregular position).edge ∉
      (chord.subarc hpath hregular position).edges := by
  intro hmem
  have hlengthOne :=
    (chord.subarc_isPath hpath hregular position).length_eq_one_of_mem_edges hmem
  have hright :
      (chord.orderedCoordinates hpath hregular position).right.val ≤
        path.length := by
    omega
  have hlength := walkInterval_length path
    (chord.orderedCoordinates hpath hregular position).left
    (chord.orderedCoordinates hpath hregular position).right
    chord.orderedCoordinates.left_lt_right.le hright
  change (walkInterval path _ _ _).length = 1 at hlengthOne
  rw [hlength] at hlengthOne
  exact (Nat.ne_of_gt
    (chord.one_lt_orderedCoordinates_span hpath hregular position))
      hlengthOne

/-- Package a cubic attachment chord as a generic chord boundary. -/
noncomputable def boundary
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position) :
    SamePathChordBoundary G where
  chord := chord.chordDart hpath hregular position
  subarc := chord.subarc hpath hregular position
  subarc_isPath := chord.subarc_isPath hpath hregular position
  chord_not_mem_subarc := chord.chord_not_mem_subarc hpath hregular position

/-! ## Coordinate support of the chord cycle -/

/-- Every vertex of the intervening chord subarc occurs at a path coordinate
between the two ordered chord endpoints. -/
theorem exists_coordinate_between_of_mem_subarc_support
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position)
    {vertex : V}
    (hvertex : vertex ∈ (chord.subarc hpath hregular position).support) :
    ∃ coordinate : Nat,
      (chord.orderedCoordinates hpath hregular position).left.val ≤ coordinate ∧
        coordinate ≤
          (chord.orderedCoordinates hpath hregular position).right.val ∧
        path.getVert coordinate = vertex := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvertex with
    ⟨offset, hoffsetVertex, hoffsetBound⟩
  have hrightBound :
      (chord.orderedCoordinates hpath hregular position).right.val ≤
        path.length := by
    exact Nat.le_of_lt_succ
      (chord.orderedCoordinates hpath hregular position).right.isLt
  have hlength := walkInterval_length path
    (chord.orderedCoordinates hpath hregular position).left
    (chord.orderedCoordinates hpath hregular position).right
    chord.orderedCoordinates.left_lt_right.le hrightBound
  have hoffsetSpan : offset ≤
      (chord.orderedCoordinates hpath hregular position).right.val -
        (chord.orderedCoordinates hpath hregular position).left.val := by
    change offset ≤ (walkInterval path _ _ _).length at hoffsetBound
    rw [hlength] at hoffsetBound
    exact hoffsetBound
  have hcoordinateRight :
      (chord.orderedCoordinates hpath hregular position).left.val + offset ≤
        (chord.orderedCoordinates hpath hregular position).right.val := by
    calc
      (chord.orderedCoordinates hpath hregular position).left.val + offset ≤
          (chord.orderedCoordinates hpath hregular position).left.val +
            ((chord.orderedCoordinates hpath hregular position).right.val -
              (chord.orderedCoordinates hpath hregular position).left.val) :=
        Nat.add_le_add_left hoffsetSpan _
      _ = (chord.orderedCoordinates hpath hregular position).right.val :=
        Nat.add_sub_of_le chord.orderedCoordinates.left_lt_right.le
  refine ⟨
    (chord.orderedCoordinates hpath hregular position).left.val + offset,
    by omega, hcoordinateRight, ?_⟩
  rw [← hoffsetVertex]
  exact (walkInterval_getVert path
    (chord.orderedCoordinates hpath hregular position).left
    (chord.orderedCoordinates hpath hregular position).right offset
    chord.orderedCoordinates.left_lt_right.le hoffsetSpan).symm

/-- Every endpoint of an edge of the chord cycle occurs at a path coordinate
between the ordered chord endpoints. -/
theorem exists_coordinate_between_of_mem_boundary_cycleWalk_edges
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position)
    (edge : G.edgeSet)
    (hedge : edge.1 ∈ (chord.boundary hpath hregular position).cycleWalk.edges)
    {vertex : V} (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    ∃ coordinate : Nat,
      (chord.orderedCoordinates hpath hregular position).left.val ≤ coordinate ∧
        coordinate ≤
          (chord.orderedCoordinates hpath hregular position).right.val ∧
        path.getVert coordinate = vertex := by
  change edge.1 ∈
    ((chord.subarc hpath hregular position).reverse.cons
      (chord.chordDart hpath hregular position).adj).edges at hedge
  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons,
    SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hedge
  rcases hedge with hedgeChord | hedgeSubarc
  · rw [hedgeChord] at hvertex
    rcases Sym2.mem_iff.mp hvertex with hleft | hright
    · exact ⟨
        (chord.orderedCoordinates hpath hregular position).left.val,
        le_rfl, chord.orderedCoordinates.left_lt_right.le, hleft.symm⟩
    · exact ⟨
        (chord.orderedCoordinates hpath hregular position).right.val,
        chord.orderedCoordinates.left_lt_right.le, le_rfl, hright.symm⟩
  · exact chord.exists_coordinate_between_of_mem_subarc_support
      hpath hregular position
      ((chord.subarc hpath hregular position).mem_support_of_mem_edges
        hedgeSubarc hvertex)

/-- Every edge incident to a path position strictly outside a chord's closed
endpoint interval avoids the chord cycle. -/
theorem incidentEdge_not_mem_boundary_cycleWalk_of_coordinate_outside
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (chord : ChordAttachment hpath hregular position)
    (coordinate : Nat) (hcoordinate : coordinate ≤ path.length)
    (houtside :
      coordinate <
          (chord.orderedCoordinates hpath hregular position).left.val ∨
        (chord.orderedCoordinates hpath hregular position).right.val <
          coordinate)
    (edge : G.edgeSet)
    (hincident : path.getVert coordinate ∈ (edge.1 : Sym2 V)) :
    edge.1 ∉ (chord.boundary hpath hregular position).cycleWalk.edges := by
  intro hedge
  rcases chord.exists_coordinate_between_of_mem_boundary_cycleWalk_edges
      hpath hregular position edge hedge hincident with
    ⟨inside, hleft, hright, hinside⟩
  have hinsideBound : inside ≤ path.length := by
    have hrightBound :=
      (chord.orderedCoordinates hpath hregular position).right.isLt
    omega
  have hcoordinates : inside = coordinate :=
    hpath.getVert_injOn hinsideBound hcoordinate hinside
  rcases houtside with hbefore | hafter <;> omega

end ChordAttachment

end Mettapedia.GraphTheory.CubicPathAttachment
