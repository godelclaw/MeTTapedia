import Mathlib.Order.Interval.Finset.Fin
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

/-- A full path coordinate is an endpoint of one of the internal chords in
the finite diagram. -/
def IsInternalChordEndpoint [DecidableRel G.Adj]
    (path : G.Walk start finish) (coordinate : Fin (path.length + 1)) : Prop :=
  ∃ chord ∈ internalChords path,
    coordinate = chord.left ∨ coordinate = chord.right

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

/-- A returning attachment reaches the boundary of the path when its other
coordinate is the initial or final path position. -/
def ReachesPathEndpoint
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (attachment : ChordAttachment hpath hregular position) : Prop :=
  attachment.otherPosition.val = 0 ∨
    attachment.otherPosition.val = path.length

/-- The canonical third edge at an internal position reaches the initial
endpoint of the path.  Unlike `ReachesPathEndpoint`, this predicate does not
depend on a chosen coordinate witness for the returning attachment. -/
def IsInitialEndpointAttachment
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : Prop :=
  attachmentNeighbor hpath hregular position = start

/-- The canonical third edge at an internal position reaches the final
endpoint of the path. -/
def IsFinalEndpointAttachment
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : Prop :=
  attachmentNeighbor hpath hregular position = finish

/-- The canonical third edge at an internal position reaches either endpoint
of the path. -/
def IsEndpointAttachment
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : Prop :=
  IsInitialEndpointAttachment hpath hregular position ∨
    IsFinalEndpointAttachment hpath hregular position

/-- A returning-coordinate witness reaches a path endpoint exactly when its
canonical third neighbour is an endpoint. -/
theorem reachesPathEndpoint_iff_isEndpointAttachment
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (attachment : ChordAttachment hpath hregular position) :
    ReachesPathEndpoint hpath hregular position attachment ↔
      IsEndpointAttachment hpath hregular position := by
  constructor
  · rintro (hzero | hfinish)
    · left
      rw [IsInitialEndpointAttachment, ← attachment.endpoint_eq]
      simpa using congrArg path.getVert hzero
    · right
      rw [IsFinalEndpointAttachment, ← attachment.endpoint_eq]
      simpa using congrArg path.getVert hfinish
  · rintro (hstart | hfinish)
    · left
      have hvertices : path.getVert attachment.otherPosition = path.getVert 0 := by
        rw [attachment.endpoint_eq, hstart, path.getVert_zero]
      exact hpath.getVert_injOn
        (Nat.lt_succ_iff.mp attachment.otherPosition.isLt)
        (Nat.zero_le path.length) hvertices
    · right
      have hvertices :
          path.getVert attachment.otherPosition = path.getVert path.length := by
        rw [attachment.endpoint_eq, hfinish, path.getVert_length]
      exact hpath.getVert_injOn
        (Nat.lt_succ_iff.mp attachment.otherPosition.isLt)
        (Nat.le_refl path.length) hvertices

/-- Internal positions whose canonical third edge reaches the initial path
endpoint. -/
noncomputable def initialEndpointAttachmentPositions
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) : Finset (InternalPosition path) :=
  Finset.univ.filter fun position =>
    attachmentNeighbor hpath hregular position = start

/-- Internal positions whose canonical third edge reaches the final path
endpoint. -/
noncomputable def finalEndpointAttachmentPositions
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) : Finset (InternalPosition path) :=
  Finset.univ.filter fun position =>
    attachmentNeighbor hpath hregular position = finish

/-- All strict internal positions whose third edge reaches a path endpoint. -/
noncomputable def endpointAttachmentPositions
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) : Finset (InternalPosition path) :=
  initialEndpointAttachmentPositions hpath hregular ∪
    finalEndpointAttachmentPositions hpath hregular

@[simp] theorem mem_initialEndpointAttachmentPositions_iff
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) (position : InternalPosition path) :
    position ∈ initialEndpointAttachmentPositions hpath hregular ↔
      IsInitialEndpointAttachment hpath hregular position := by
  simp [initialEndpointAttachmentPositions, IsInitialEndpointAttachment]

@[simp] theorem mem_finalEndpointAttachmentPositions_iff
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) (position : InternalPosition path) :
    position ∈ finalEndpointAttachmentPositions hpath hregular ↔
      IsFinalEndpointAttachment hpath hregular position := by
  simp [finalEndpointAttachmentPositions, IsFinalEndpointAttachment]

@[simp] theorem mem_endpointAttachmentPositions_iff
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) (position : InternalPosition path) :
    position ∈ endpointAttachmentPositions hpath hregular ↔
      IsEndpointAttachment hpath hregular position := by
  simp [endpointAttachmentPositions, IsEndpointAttachment]

/-- Distinct internal coordinates of a simple path represent distinct
vertices. -/
theorem internalPosition_vertex_injective
    {path : G.Walk start finish} (hpath : path.IsPath) :
    Function.Injective (fun position : InternalPosition path => position.vertex) := by
  intro first second hvertices
  apply Fin.ext
  have hindices := hpath.getVert_injOn
    (Nat.le_of_lt first.index_lt_length)
    (Nat.le_of_lt second.index_lt_length) hvertices
  change first.val + 1 = second.val + 1 at hindices
  omega

/-- At most two internal third edges can return to the initial endpoint of a
simple cubic path: the first path edge already occupies the third incident
slot. -/
theorem card_initialEndpointAttachmentPositions_le_two
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) :
    (initialEndpointAttachmentPositions hpath hregular).card ≤ 2 := by
  by_cases hpositive : 0 < path.length
  · let firstNeighbor := path.getVert 1
    have hfirstNeighbor : firstNeighbor ∈ G.neighborFinset start := by
      simpa [firstNeighbor] using path.adj_getVert_succ hpositive
    have hsubset :
        (initialEndpointAttachmentPositions hpath hregular).image
            (fun position => position.vertex) ⊆
          (G.neighborFinset start).erase firstNeighbor := by
      intro vertex hvertex
      rcases Finset.mem_image.mp hvertex with ⟨position, hposition, rfl⟩
      have hinitial :=
        (mem_initialEndpointAttachmentPositions_iff hpath hregular position).mp
          hposition
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        have hindex : position.index = 1 := hpath.getVert_injOn
          (Nat.le_of_lt position.index_lt_length)
          hpositive heq
        exact attachmentNeighbor_ne_previousVertex hpath hregular position (by
          rw [hinitial]
          simp [InternalPosition.previousVertex, hindex])
      · have hadj := (attachmentNeighbor_adj hpath hregular position).symm
        rw [hinitial] at hadj
        simpa only [SimpleGraph.mem_neighborFinset] using hadj
    calc
      (initialEndpointAttachmentPositions hpath hregular).card =
          ((initialEndpointAttachmentPositions hpath hregular).image
            (fun position => position.vertex)).card := by
              symm
              exact Finset.card_image_iff.mpr
                (internalPosition_vertex_injective hpath).injOn
      _ ≤ ((G.neighborFinset start).erase firstNeighbor).card :=
        Finset.card_le_card hsubset
      _ = (G.neighborFinset start).card - 1 :=
        Finset.card_erase_of_mem hfirstNeighbor
      _ = 2 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree,
          hregular.degree_eq]
  · have hzero : path.length = 0 := Nat.eq_zero_of_not_pos hpositive
    calc
      (initialEndpointAttachmentPositions hpath hregular).card ≤
          (Finset.univ : Finset (InternalPosition path)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card (InternalPosition path) := Finset.card_univ
      _ = 0 := by simp [InternalPosition.card_internalPosition, hzero]
      _ ≤ 2 := by omega

/-- At most two internal third edges can return to the final endpoint of a
simple cubic path. -/
theorem card_finalEndpointAttachmentPositions_le_two
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) :
    (finalEndpointAttachmentPositions hpath hregular).card ≤ 2 := by
  by_cases hpositive : 0 < path.length
  · let lastNeighbor := path.getVert (path.length - 1)
    have hlastLt : path.length - 1 < path.length := Nat.sub_lt hpositive Nat.one_pos
    have hlastSucc : path.length - 1 + 1 = path.length :=
      Nat.sub_add_cancel hpositive
    have hlastNeighbor : lastNeighbor ∈ G.neighborFinset finish := by
      simpa [lastNeighbor, hlastSucc] using
        (path.adj_getVert_succ hlastLt).symm
    have hsubset :
        (finalEndpointAttachmentPositions hpath hregular).image
            (fun position => position.vertex) ⊆
          (G.neighborFinset finish).erase lastNeighbor := by
      intro vertex hvertex
      rcases Finset.mem_image.mp hvertex with ⟨position, hposition, rfl⟩
      have hfinal :=
        (mem_finalEndpointAttachmentPositions_iff hpath hregular position).mp
          hposition
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        have hindex : position.index = path.length - 1 :=
          hpath.getVert_injOn
            (Nat.le_of_lt position.index_lt_length)
            (Nat.sub_le path.length 1) heq
        have hnext : position.index + 1 = path.length := by omega
        exact attachmentNeighbor_ne_nextVertex hpath hregular position (by
          rw [hfinal]
          simp [InternalPosition.nextVertex, hnext])
      · have hadj := (attachmentNeighbor_adj hpath hregular position).symm
        rw [hfinal] at hadj
        simpa only [SimpleGraph.mem_neighborFinset] using hadj
    calc
      (finalEndpointAttachmentPositions hpath hregular).card =
          ((finalEndpointAttachmentPositions hpath hregular).image
            (fun position => position.vertex)).card := by
              symm
              exact Finset.card_image_iff.mpr
                (internalPosition_vertex_injective hpath).injOn
      _ ≤ ((G.neighborFinset finish).erase lastNeighbor).card :=
        Finset.card_le_card hsubset
      _ = (G.neighborFinset finish).card - 1 :=
        Finset.card_erase_of_mem hlastNeighbor
      _ = 2 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree,
          hregular.degree_eq]
  · have hzero : path.length = 0 := Nat.eq_zero_of_not_pos hpositive
    calc
      (finalEndpointAttachmentPositions hpath hregular).card ≤
          (Finset.univ : Finset (InternalPosition path)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card (InternalPosition path) := Finset.card_univ
      _ = 0 := by simp [InternalPosition.card_internalPosition, hzero]
      _ ≤ 2 := by omega

/-- The two path endpoints account for at most four exceptional returning
attachments in total. -/
theorem card_endpointAttachmentPositions_le_four
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) :
    (endpointAttachmentPositions hpath hregular).card ≤ 4 := by
  calc
    (endpointAttachmentPositions hpath hregular).card ≤
        (initialEndpointAttachmentPositions hpath hregular).card +
          (finalEndpointAttachmentPositions hpath hregular).card :=
      Finset.card_union_le _ _
    _ ≤ 2 + 2 := Nat.add_le_add
      (card_initialEndpointAttachmentPositions_le_two hpath hregular)
      (card_finalEndpointAttachmentPositions_le_two hpath hregular)
    _ = 4 := rfl

/-- The internal path coordinates that are not among the at-most-four
endpoint-return exceptions. -/
noncomputable def internalNonendpointCoordinates
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) :
    Finset (Fin (path.length + 1)) :=
  ((Finset.univ : Finset (InternalPosition path)) \
      endpointAttachmentPositions hpath hregular).image
    InternalPosition.coordinate

/-- The coordinate embedding of strict internal path positions is
injective. -/
theorem internalPosition_coordinate_injective
    {path : G.Walk start finish} :
    Function.Injective
      (InternalPosition.coordinate : InternalPosition path →
        Fin (path.length + 1)) := by
  intro first second heq
  apply Fin.ext
  have hval := Fin.ext_iff.mp heq
  change first.val + 1 = second.val + 1 at hval
  omega

/-- Exact cardinality of the sweepable coordinate set. -/
theorem card_internalNonendpointCoordinates
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) :
    (internalNonendpointCoordinates hpath hregular).card =
      Fintype.card (InternalPosition path) -
        (endpointAttachmentPositions hpath hregular).card := by
  rw [internalNonendpointCoordinates,
    Finset.card_image_iff.mpr internalPosition_coordinate_injective.injOn,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]

/-- Removing every possible endpoint-return exception still leaves at least
`length - 5` strict internal coordinates. -/
theorem path_length_sub_five_le_card_internalNonendpointCoordinates
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3) :
    path.length - 5 ≤
      (internalNonendpointCoordinates hpath hregular).card := by
  rw [card_internalNonendpointCoordinates,
    InternalPosition.card_internalPosition]
  have hendpoint := card_endpointAttachmentPositions_le_four hpath hregular
  omega

/-- Inside any internal chord, all but at most four path coordinates belong
to the non-endpoint attachment sweep.  Equivalently, the chord span is at most
the number of sweep-eligible coordinates in its open interval plus five. -/
theorem OrderedPathChord.span_le_card_internalNonendpointCoordinates_inside_add_five
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) :
    chord.right.val - chord.left.val ≤
      ((internalNonendpointCoordinates hpath hregular).filter
        fun coordinate =>
          chord.left < coordinate ∧ coordinate < chord.right).card + 5 := by
  let exceptionalCoordinates : Finset (Fin (path.length + 1)) :=
    (endpointAttachmentPositions hpath hregular).image
      InternalPosition.coordinate
  have hcover :
      Finset.Ioo chord.left chord.right ⊆
        (internalNonendpointCoordinates hpath hregular).filter
            (fun coordinate =>
              chord.left < coordinate ∧ coordinate < chord.right) ∪
          exceptionalCoordinates := by
    intro coordinate hcoordinate
    have hinside := Finset.mem_Ioo.mp hcoordinate
    let position : InternalPosition path :=
      ⟨coordinate.val - 1, by
        have hleftPositive := hchord.1
        have hrightBound := hchord.2.1
        have hcoordinatePositive : 0 < coordinate.val :=
          lt_trans hleftPositive hinside.1
        have hcoordinateBound : coordinate.val < path.length :=
          lt_trans hinside.2 hrightBound
        omega⟩
    have hpositionCoordinate : position.coordinate = coordinate := by
      apply Fin.ext
      simp only [InternalPosition.coordinate_val, InternalPosition.index,
        position]
      have hleftPositive := hchord.1
      have hcoordinatePositive : 0 < coordinate.val :=
        lt_trans hleftPositive hinside.1
      omega
    by_cases hposition :
        position ∈ endpointAttachmentPositions hpath hregular
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr
        ⟨position, hposition, hpositionCoordinate⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨?_, hinside⟩
      rw [internalNonendpointCoordinates]
      exact Finset.mem_image.mpr
        ⟨position, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hposition⟩,
          hpositionCoordinate⟩
  have hinterval :
      (Finset.Ioo chord.left chord.right).card ≤
        ((internalNonendpointCoordinates hpath hregular).filter
          fun coordinate =>
            chord.left < coordinate ∧ coordinate < chord.right).card + 4 := by
    calc
      (Finset.Ioo chord.left chord.right).card ≤
          ((internalNonendpointCoordinates hpath hregular).filter
              (fun coordinate =>
                chord.left < coordinate ∧ coordinate < chord.right) ∪
            exceptionalCoordinates).card := Finset.card_le_card hcover
      _ ≤ ((internalNonendpointCoordinates hpath hregular).filter
              fun coordinate =>
                chord.left < coordinate ∧ coordinate < chord.right).card +
            exceptionalCoordinates.card := Finset.card_union_le _ _
      _ ≤ ((internalNonendpointCoordinates hpath hregular).filter
              fun coordinate =>
                chord.left < coordinate ∧ coordinate < chord.right).card + 4 := by
        apply Nat.add_le_add_left
        exact Finset.card_image_le.trans
          (card_endpointAttachmentPositions_le_four hpath hregular)
  rw [Fin.card_Ioo] at hinterval
  have hspan := hchord.2.2.1
  omega

/-- Every strict internal position belongs to exactly the geometric universe
needed by an attachment sweep: its third edge leaves the path, reaches a path
endpoint, or is represented by an internal chord incident to that position.

The alternatives are stated as an inclusive disjunction because only their
coverage, not a chosen decision procedure, is needed downstream. -/
theorem external_or_reachesEndpoint_or_mem_internalChord
    [DecidableEq V] [DecidableRel G.Adj]
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    IsExternalAttachment hpath hregular position ∨
      ∃ attachment : ChordAttachment hpath hregular position,
        ReachesPathEndpoint hpath hregular position attachment ∨
          ∃ chord ∈ internalChords path,
            position.coordinate = chord.left ∨
              position.coordinate = chord.right := by
  rcases chordAttachment_or_externalAttachment hpath hregular position with
    ⟨⟨attachment⟩⟩ | hexternal
  · right
    refine ⟨attachment, ?_⟩
    by_cases hendpoint :
        ReachesPathEndpoint hpath hregular position attachment
    · exact Or.inl hendpoint
    · right
      let chord := attachment.orderedCoordinates hpath hregular position
      have hotherPositive : 0 < attachment.otherPosition.val := by
        have hnotZero : attachment.otherPosition.val ≠ 0 := by
          intro hzero
          exact hendpoint (Or.inl hzero)
        omega
      have hotherLt : attachment.otherPosition.val < path.length := by
        have hle : attachment.otherPosition.val ≤ path.length :=
          Nat.lt_succ_iff.mp attachment.otherPosition.isLt
        have hnotFinish : attachment.otherPosition.val ≠ path.length := by
          intro hfinish
          exact hendpoint (Or.inr hfinish)
        omega
      have hpositionPositive : 0 < position.coordinate.val := by
        change 0 < position.index
        exact Nat.pos_of_ne_zero position.index_ne_zero
      have hpositionLt : position.coordinate.val < path.length := by
        simp [InternalPosition.coordinate]
      have hinternal : IsInternalChord chord := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · by_cases horder : position.coordinate < attachment.otherPosition
          · simpa [chord, ChordAttachment.orderedCoordinates, horder] using
              hpositionPositive
          · simpa [chord, ChordAttachment.orderedCoordinates, horder] using
              hotherPositive
        · by_cases horder : position.coordinate < attachment.otherPosition
          · simpa [chord, ChordAttachment.orderedCoordinates, horder] using
              hotherLt
          · simpa [chord, ChordAttachment.orderedCoordinates, horder] using
              hpositionLt
        · exact attachment.one_lt_orderedCoordinates_span
            hpath hregular position
        · exact attachment.getVert_orderedCoordinates_adj
            hpath hregular position
      refine ⟨chord, mem_internalChords_iff.mpr hinternal, ?_⟩
      exact attachment.coordinate_eq_left_or_right hpath hregular position
  · exact Or.inl hexternal

/-- Witness-free form of the attachment trichotomy.  Every internal position
is external, is one of the at-most-four endpoint exceptions, or is incident
to an internal chord of the finite diagram. -/
theorem external_or_endpoint_or_mem_internalChord
    [DecidableEq V] [DecidableRel G.Adj]
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    IsExternalAttachment hpath hregular position ∨
      IsEndpointAttachment hpath hregular position ∨
        ∃ chord ∈ internalChords path,
          position.coordinate = chord.left ∨
            position.coordinate = chord.right := by
  rcases external_or_reachesEndpoint_or_mem_internalChord
      hpath hregular position with
    hexternal | ⟨attachment, hendpoint | hchord⟩
  · exact Or.inl hexternal
  · exact Or.inr (Or.inl
      ((reachesPathEndpoint_iff_isEndpointAttachment
        hpath hregular position attachment).mp hendpoint))
  · exact Or.inr (Or.inr hchord)

/-- If external attachments are absent, every nonexceptional internal
coordinate is an endpoint of the finite internal-chord diagram. -/
theorem isInternalChordEndpoint_of_mem_internalNonendpointCoordinates
    [DecidableEq V] [DecidableRel G.Adj]
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (hnoExternal : ∀ position : InternalPosition path,
      ¬IsExternalAttachment hpath hregular position)
    {coordinate : Fin (path.length + 1)}
    (hcoordinate :
      coordinate ∈ internalNonendpointCoordinates hpath hregular) :
    IsInternalChordEndpoint path coordinate := by
  rcases Finset.mem_image.mp hcoordinate with
    ⟨position, hposition, hpositionCoordinate⟩
  have hnotEndpoint :
      ¬IsEndpointAttachment hpath hregular position := by
    intro hendpoint
    exact (Finset.mem_sdiff.mp hposition).2
      ((mem_endpointAttachmentPositions_iff hpath hregular position).mpr
        hendpoint)
  rcases external_or_endpoint_or_mem_internalChord
      hpath hregular position with
    hexternal | hendpoint | ⟨chord, hchord, hincident⟩
  · exact False.elim (hnoExternal position hexternal)
  · exact False.elim (hnotEndpoint hendpoint)
  · exact ⟨chord, hchord, by
      simpa only [← hpositionCoordinate] using hincident⟩

end Mettapedia.GraphTheory.CubicPathChordDiagram
