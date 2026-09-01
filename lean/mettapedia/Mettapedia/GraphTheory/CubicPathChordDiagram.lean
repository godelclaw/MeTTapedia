import Mettapedia.GraphTheory.CubicPathChord

/-!
# The internal chord diagram of a cubic path

A nonconsecutive graph edge between two strict internal positions of a simple
path is a chord at both endpoints.  In a cubic graph these internal chords
form a partial matching: the two path edges already consume two of the three
edges at every internal vertex, leaving room for exactly one chord endpoint.

The definitions in this file expose the finite ordered-coordinate diagram;
they do not assume a planar embedding or a rotation system.
-/

namespace Mettapedia.GraphTheory.CubicPathChordDiagram

open CubicPathAttachment
open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {start finish : V}

/-- An ordered path chord is an internal graph chord when both endpoints are
strict internal path positions, its span is at least two path edges, and its
endpoint vertices are adjacent in the ambient graph. -/
def IsInternalChord {path : G.Walk start finish}
    (chord : OrderedPathChord (path.length + 1)) : Prop :=
  0 < chord.left.val ∧ chord.right.val < path.length ∧
    1 < chord.right.val - chord.left.val ∧
    G.Adj (path.getVert chord.left) (path.getVert chord.right)

instance [DecidableRel G.Adj] {path : G.Walk start finish}
    (chord : OrderedPathChord (path.length + 1)) :
    Decidable (IsInternalChord chord) := by
  unfold IsInternalChord
  infer_instance

/-- All internal graph chords of a finite path, represented only by their
ordered endpoint coordinates. -/
def internalChords [DecidableRel G.Adj] (path : G.Walk start finish) :
    Finset (OrderedPathChord (path.length + 1)) :=
  Finset.univ.filter IsInternalChord

@[simp] theorem mem_internalChords_iff [DecidableRel G.Adj]
    {path : G.Walk start finish}
    {chord : OrderedPathChord (path.length + 1)} :
    chord ∈ internalChords path ↔ IsInternalChord chord := by
  simp [internalChords]

/-- The left coordinate of an internal chord, viewed in the intrinsic type of
strict internal path positions. -/
def leftPosition {path : G.Walk start finish}
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) : InternalPosition path :=
  ⟨chord.left.val - 1, by
    have hleftPositive := hchord.1
    have hrightBound := hchord.2.1
    have horder := chord.left_lt_right
    omega⟩

/-- The right coordinate of an internal chord, viewed in the intrinsic type
of strict internal path positions. -/
def rightPosition {path : G.Walk start finish}
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) : InternalPosition path :=
  ⟨chord.right.val - 1, by
    have hrightPositive : 0 < chord.right.val :=
      lt_trans hchord.1 chord.left_lt_right
    have hrightBound := hchord.2.1
    omega⟩

@[simp] theorem leftPosition_index {path : G.Walk start finish}
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) :
    (leftPosition chord hchord).index = chord.left.val := by
  have hleftPositive := hchord.1
  simp [leftPosition, InternalPosition.index]
  omega

@[simp] theorem rightPosition_index {path : G.Walk start finish}
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) :
    (rightPosition chord hchord).index = chord.right.val := by
  have hrightPositive : 0 < chord.right.val :=
    lt_trans hchord.1 chord.left_lt_right
  simp [rightPosition, InternalPosition.index]
  omega

@[simp] theorem leftPosition_coordinate {path : G.Walk start finish}
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) :
    (leftPosition chord hchord).coordinate = chord.left := by
  apply Fin.ext
  exact leftPosition_index chord hchord

@[simp] theorem rightPosition_coordinate {path : G.Walk start finish}
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) :
    (rightPosition chord hchord).coordinate = chord.right := by
  apply Fin.ext
  exact rightPosition_index chord hchord

variable [G.LocallyFinite]

/-- An internal graph chord presented as the canonical third-edge attachment
at its earlier endpoint. -/
noncomputable def leftAttachment
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) :
    ChordAttachment hpath hregular (leftPosition chord hchord) where
  otherPosition := chord.right
  endpoint_eq := by
    have hadj := hchord.2.2.2
    have hspan := hchord.2.2.1
    apply getVert_eq_attachmentNeighbor_of_adj_of_nonconsecutive
      hpath hregular
    · simpa [InternalPosition.vertex] using hadj
    · rw [leftPosition_index]
      omega
    · rw [leftPosition_index]
      omega
  not_previous := by
    have horder := chord.left_lt_right
    rw [leftPosition_index]
    omega
  not_next := by
    have hspan := hchord.2.2.1
    rw [leftPosition_index]
    omega

/-- The same internal graph chord presented as the canonical third-edge
attachment at its later endpoint. -/
noncomputable def rightAttachment
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) :
    ChordAttachment hpath hregular (rightPosition chord hchord) where
  otherPosition := chord.left
  endpoint_eq := by
    have hadj := hchord.2.2.2
    have hspan := hchord.2.2.1
    apply getVert_eq_attachmentNeighbor_of_adj_of_nonconsecutive
      hpath hregular
    · simpa [InternalPosition.vertex] using hadj.symm
    · rw [rightPosition_index]
      omega
    · rw [rightPosition_index]
      omega
  not_previous := by
    have hspan := hchord.2.2.1
    rw [rightPosition_index]
    omega
  not_next := by
    have horder := chord.left_lt_right
    rw [rightPosition_index]
    omega

@[simp] theorem leftAttachment_orderedCoordinates
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) :
    (leftAttachment hpath hregular chord hchord).orderedCoordinates
      hpath hregular (leftPosition chord hchord) = chord := by
  simp [ChordAttachment.orderedCoordinates, leftAttachment,
    chord.left_lt_right]

@[simp] theorem leftAttachment_isLeftEndpoint
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) :
    (leftAttachment hpath hregular chord hchord).IsLeftEndpoint
      hpath hregular (leftPosition chord hchord) := by
  rw [ChordAttachment.IsLeftEndpoint,
    leftAttachment_orderedCoordinates]
  exact leftPosition_coordinate chord hchord

private theorem eq_of_left_eq_left
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    {first second : OrderedPathChord (path.length + 1)}
    (hfirst : IsInternalChord first) (hsecond : IsInternalChord second)
    (hleft : first.left = second.left) : first = second := by
  have hpositions : leftPosition first hfirst = leftPosition second hsecond := by
    apply Fin.ext
    simp [leftPosition, hleft]
  have hfirstEndpoint := (leftAttachment hpath hregular first hfirst).endpoint_eq
  have hsecondEndpoint :=
    (leftAttachment hpath hregular second hsecond).endpoint_eq
  change path.getVert first.right =
    attachmentNeighbor hpath hregular (leftPosition first hfirst) at hfirstEndpoint
  change path.getVert second.right =
    attachmentNeighbor hpath hregular (leftPosition second hsecond) at hsecondEndpoint
  have hvertices : path.getVert first.right = path.getVert second.right := by
    calc
      path.getVert first.right =
          attachmentNeighbor hpath hregular (leftPosition first hfirst) :=
        hfirstEndpoint
      _ = attachmentNeighbor hpath hregular (leftPosition second hsecond) := by
        rw [hpositions]
      _ = path.getVert second.right := hsecondEndpoint.symm
  have hright : first.right.val = second.right.val :=
    hpath.getVert_injOn (Nat.le_of_lt hfirst.2.1)
      (Nat.le_of_lt hsecond.2.1) hvertices
  have hrightFin : first.right = second.right := Fin.ext hright
  cases first with
  | mk firstLeft firstRight firstOrder =>
    cases second with
    | mk secondLeft secondRight secondOrder =>
      simp only at hleft hrightFin
      subst secondLeft
      subst secondRight
      rfl

private theorem eq_of_right_eq_right
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    {first second : OrderedPathChord (path.length + 1)}
    (hfirst : IsInternalChord first) (hsecond : IsInternalChord second)
    (hright : first.right = second.right) : first = second := by
  have hpositions : rightPosition first hfirst = rightPosition second hsecond := by
    apply Fin.ext
    simp [rightPosition, hright]
  have hfirstEndpoint := (rightAttachment hpath hregular first hfirst).endpoint_eq
  have hsecondEndpoint :=
    (rightAttachment hpath hregular second hsecond).endpoint_eq
  change path.getVert first.left =
    attachmentNeighbor hpath hregular (rightPosition first hfirst) at hfirstEndpoint
  change path.getVert second.left =
    attachmentNeighbor hpath hregular (rightPosition second hsecond) at hsecondEndpoint
  have hvertices : path.getVert first.left = path.getVert second.left := by
    calc
      path.getVert first.left =
          attachmentNeighbor hpath hregular (rightPosition first hfirst) :=
        hfirstEndpoint
      _ = attachmentNeighbor hpath hregular (rightPosition second hsecond) := by
        rw [hpositions]
      _ = path.getVert second.left := hsecondEndpoint.symm
  have hleft : first.left.val = second.left.val :=
    hpath.getVert_injOn (by exact Nat.le_of_lt (lt_trans first.left_lt_right hfirst.2.1))
      (by exact Nat.le_of_lt (lt_trans second.left_lt_right hsecond.2.1)) hvertices
  have hleftFin : first.left = second.left := Fin.ext hleft
  cases first with
  | mk firstLeft firstRight firstOrder =>
    cases second with
    | mk secondLeft secondRight secondOrder =>
      simp only at hright hleftFin
      subst secondLeft
      subst secondRight
      rfl

private theorem left_ne_right
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    {first second : OrderedPathChord (path.length + 1)}
    (hfirst : IsInternalChord first) (hsecond : IsInternalChord second) :
    first.left ≠ second.right := by
  intro hcommon
  have hpositions : leftPosition first hfirst = rightPosition second hsecond := by
    apply Fin.ext
    simp [leftPosition, rightPosition, hcommon]
  have hfirstEndpoint := (leftAttachment hpath hregular first hfirst).endpoint_eq
  have hsecondEndpoint :=
    (rightAttachment hpath hregular second hsecond).endpoint_eq
  change path.getVert first.right =
    attachmentNeighbor hpath hregular (leftPosition first hfirst) at hfirstEndpoint
  change path.getVert second.left =
    attachmentNeighbor hpath hregular (rightPosition second hsecond) at hsecondEndpoint
  have hvertices : path.getVert first.right = path.getVert second.left := by
    calc
      path.getVert first.right =
          attachmentNeighbor hpath hregular (leftPosition first hfirst) :=
        hfirstEndpoint
      _ = attachmentNeighbor hpath hregular (rightPosition second hsecond) := by
        rw [hpositions]
      _ = path.getVert second.left := hsecondEndpoint.symm
  have hother : first.right.val = second.left.val :=
    hpath.getVert_injOn (Nat.le_of_lt hfirst.2.1)
      (Nat.le_of_lt (lt_trans second.left_lt_right hsecond.2.1)) hvertices
  have hfirstOrder := first.left_lt_right
  have hsecondOrder := second.left_lt_right
  omega

/-- The internal graph chords of a simple cubic path share no endpoints.
Thus their coordinate diagram is intrinsically a partial matching, before
any planar noncrossing information is added. -/
theorem pairwiseEndpointDisjoint_internalChords
    [DecidableRel G.Adj] {path : G.Walk start finish}
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3) :
    PairwiseEndpointDisjoint (internalChords path) := by
  intro first hfirstMem second hsecondMem hne
  have hfirst := mem_internalChords_iff.mp hfirstMem
  have hsecond := mem_internalChords_iff.mp hsecondMem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hleft
    exact hne (eq_of_left_eq_left hpath hregular hfirst hsecond hleft)
  · exact left_ne_right hpath hregular hfirst hsecond
  · intro hrightLeft
    exact left_ne_right hpath hregular hsecond hfirst hrightLeft.symm
  · intro hright
    exact hne (eq_of_right_eq_right hpath hregular hfirst hsecond hright)

end Mettapedia.GraphTheory.CubicPathChordDiagram
