import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Attachments to a path in a cubic graph

At an internal vertex of a simple path, two of the three incident edges are
the path edges.  This file identifies the unique remaining neighbour and
classifies it as either another vertex of the path (a chord) or a vertex
outside the path (an external attachment).

The definitions are graph-theoretic: they do not assume planarity, a rotation
system, or a colouring.
-/

namespace Mettapedia.GraphTheory.CubicPathAttachment

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {start finish : V}

/-- A strict internal position of a walk.  The value `i : Fin (length - 1)`
denotes path coordinate `i + 1`, making both endpoint exclusions intrinsic to
the type. -/
abbrev InternalPosition (path : G.Walk start finish) := Fin (path.length - 1)

namespace InternalPosition

/-- The natural-number coordinate of an internal path position. -/
def index {path : G.Walk start finish} (position : InternalPosition path) : Nat :=
  position.val + 1

@[simp] theorem index_ne_zero {path : G.Walk start finish}
    (position : InternalPosition path) : position.index ≠ 0 := by
  simp [index]

@[simp] theorem index_lt_length {path : G.Walk start finish}
    (position : InternalPosition path) : position.index < path.length := by
  have := position.isLt
  simp only [index]
  omega

@[simp] theorem card_internalPosition (path : G.Walk start finish) :
    Fintype.card (InternalPosition path) = path.length - 1 :=
  Fintype.card_fin _

/-- The path vertex at an internal position. -/
def vertex {path : G.Walk start finish} (position : InternalPosition path) : V :=
  path.getVert position.index

/-- The preceding path vertex. -/
def previousVertex {path : G.Walk start finish}
    (position : InternalPosition path) : V :=
  path.getVert (position.index - 1)

/-- The following path vertex. -/
def nextVertex {path : G.Walk start finish}
    (position : InternalPosition path) : V :=
  path.getVert (position.index + 1)

end InternalPosition

/-- A simple path has exactly two fewer internal positions than distinct
support vertices, with truncated subtraction covering the degenerate cases. -/
theorem card_internalPosition_eq_support_toFinset_card_sub_two
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath) :
    Fintype.card (InternalPosition path) = path.support.toFinset.card - 2 := by
  rw [InternalPosition.card_internalPosition,
    List.toFinset_card_of_nodup hpath.support_nodup, path.length_support]
  omega

/-- A lower bound on distinct support vertices gives the corresponding lower
bound on strict internal positions. -/
theorem lt_card_internalPosition_of_add_two_lt_support_toFinset_card
    [DecidableEq V] {path : G.Walk start finish} (hpath : path.IsPath)
    {bound : Nat} (hlong : bound + 2 < path.support.toFinset.card) :
    bound < Fintype.card (InternalPosition path) := by
  rw [card_internalPosition_eq_support_toFinset_card_sub_two hpath]
  omega

variable [G.LocallyFinite]

/-- Neighbours joined to an internal vertex by an edge not traversed by the
path.  A member may still be a different vertex of the path, in which case the
remaining edge is a chord. -/
def attachmentNeighborSet (path : G.Walk start finish)
    (position : InternalPosition path) : Set V :=
  G.neighborSet position.vertex \
    path.toSubgraph.neighborSet position.vertex

/-- In a cubic graph, a simple path has exactly one attachment neighbour at
each internal position. -/
theorem ncard_attachmentNeighborSet_eq_one
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    (attachmentNeighborSet path position).ncard = 1 := by
  have hsubset :
      path.toSubgraph.neighborSet position.vertex ⊆
        G.neighborSet position.vertex :=
    path.toSubgraph.neighborSet_subset position.vertex
  have hpathCard :
      (path.toSubgraph.neighborSet position.vertex).ncard = 2 := by
    simpa [InternalPosition.vertex] using
      hpath.ncard_neighborSet_toSubgraph_internal_eq_two
        position.index_ne_zero position.index_lt_length
  have hambientCard : (G.neighborSet position.vertex).ncard = 3 := by
    rw [← Set.fintypeCard_eq_ncard,
      SimpleGraph.card_neighborSet_eq_degree, hregular.degree_eq]
  have hsplit := Set.ncard_sdiff_add_ncard_of_subset hsubset
  change (attachmentNeighborSet path position).ncard +
      (path.toSubgraph.neighborSet position.vertex).ncard =
        (G.neighborSet position.vertex).ncard at hsplit
  omega

/-- The unique neighbour reached by the third edge at an internal position of
a simple path in a cubic graph. -/
noncomputable def attachmentNeighbor
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : V :=
  Classical.choose (Set.ncard_eq_one.mp
    (ncard_attachmentNeighborSet_eq_one hpath hregular position))

theorem attachmentNeighborSet_eq_singleton
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    attachmentNeighborSet path position =
      {attachmentNeighbor hpath hregular position} :=
  Classical.choose_spec (Set.ncard_eq_one.mp
    (ncard_attachmentNeighborSet_eq_one hpath hregular position))

theorem attachmentNeighbor_mem
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    attachmentNeighbor hpath hregular position ∈
      attachmentNeighborSet path position := by
  rw [attachmentNeighborSet_eq_singleton hpath hregular position]
  simp

theorem eq_attachmentNeighbor_of_mem
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) {neighbor : V}
    (hneighbor : neighbor ∈ attachmentNeighborSet path position) :
    neighbor = attachmentNeighbor hpath hregular position := by
  rw [attachmentNeighborSet_eq_singleton hpath hregular position] at hneighbor
  simpa using hneighbor

theorem attachmentNeighbor_adj
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    G.Adj position.vertex (attachmentNeighbor hpath hregular position) :=
  (attachmentNeighbor_mem hpath hregular position).1

theorem attachmentNeighbor_not_mem_pathNeighborSet
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    attachmentNeighbor hpath hregular position ∉
      path.toSubgraph.neighborSet position.vertex :=
  (attachmentNeighbor_mem hpath hregular position).2

/-- The third edge at an internal path position. -/
noncomputable def attachmentEdge
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : G.edgeSet :=
  ⟨s(position.vertex, attachmentNeighbor hpath hregular position),
    attachmentNeighbor_adj hpath hregular position⟩

theorem attachmentNeighbor_ne_previousVertex
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    attachmentNeighbor hpath hregular position ≠ position.previousVertex := by
  intro heq
  apply attachmentNeighbor_not_mem_pathNeighborSet hpath hregular position
  change attachmentNeighbor hpath hregular position ∈
    path.toSubgraph.neighborSet (path.getVert position.index)
  rw [hpath.neighborSet_toSubgraph_internal
    position.index_ne_zero position.index_lt_length, heq]
  simp [InternalPosition.previousVertex]

theorem attachmentNeighbor_ne_nextVertex
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    attachmentNeighbor hpath hregular position ≠ position.nextVertex := by
  intro heq
  apply attachmentNeighbor_not_mem_pathNeighborSet hpath hregular position
  change attachmentNeighbor hpath hregular position ∈
    path.toSubgraph.neighborSet (path.getVert position.index)
  rw [hpath.neighborSet_toSubgraph_internal
    position.index_ne_zero position.index_lt_length, heq]
  simp [InternalPosition.nextVertex]

/-- Any nonconsecutive path vertex adjacent to an internal path vertex is the
unique third-edge neighbour there.  This representation-independent form is
useful when a chord is first presented by its two path coordinates rather
than by an `attachmentNeighbor` witness. -/
theorem getVert_eq_attachmentNeighbor_of_adj_of_nonconsecutive
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (other : Fin (path.length + 1))
    (hadj : G.Adj position.vertex (path.getVert other))
    (hprevious : other.val ≠ position.index - 1)
    (hnext : other.val ≠ position.index + 1) :
    path.getVert other = attachmentNeighbor hpath hregular position := by
  apply eq_attachmentNeighbor_of_mem hpath hregular position
  refine ⟨hadj, ?_⟩
  change path.getVert other ∉
    path.toSubgraph.neighborSet (path.getVert position.index)
  rw [hpath.neighborSet_toSubgraph_internal
    position.index_ne_zero position.index_lt_length]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  push Not
  constructor
  · intro heq
    have hcoordinate := hpath.getVert_injOn
      (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt position.index_lt_length))
      (Nat.lt_succ_iff.mp other.isLt) heq.symm
    exact hprevious hcoordinate.symm
  · intro heq
    have hnextBound : position.index + 1 ≤ path.length := by
      exact position.index_lt_length
    have hcoordinate := hpath.getVert_injOn hnextBound
      (Nat.lt_succ_iff.mp other.isLt) heq.symm
    exact hnext hcoordinate.symm

/-- A coordinate witnessing that the third edge at an internal position is a
chord.  Its other endpoint is neither adjacent path position. -/
structure ChordAttachment
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) where
  otherPosition : Fin (path.length + 1)
  endpoint_eq :
    path.getVert otherPosition = attachmentNeighbor hpath hregular position
  not_previous : otherPosition.val ≠ position.index - 1
  not_next : otherPosition.val ≠ position.index + 1

/-- Otherwise the third edge leaves the path support. -/
def IsExternalAttachment
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : Prop :=
  attachmentNeighbor hpath hregular position ∉ path.support

/-- **Chord/external-attachment classification.**  The unique third edge at
an internal vertex either returns to one nonconsecutive position of the same
path or leaves the path support. -/
theorem chordAttachment_or_externalAttachment
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    Nonempty (ChordAttachment hpath hregular position) ∨
      IsExternalAttachment hpath hregular position := by
  by_cases hsupport :
      attachmentNeighbor hpath hregular position ∈ path.support
  · left
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hsupport with
      ⟨other, hother, hle⟩
    let otherPosition : Fin (path.length + 1) :=
      ⟨other, Nat.lt_succ_iff.mpr hle⟩
    have hprevious : otherPosition.val ≠ position.index - 1 := by
      intro heq
      apply attachmentNeighbor_ne_previousVertex hpath hregular position
      rw [← hother]
      simpa [otherPosition, InternalPosition.previousVertex] using
        congrArg path.getVert heq
    have hnext : otherPosition.val ≠ position.index + 1 := by
      intro heq
      apply attachmentNeighbor_ne_nextVertex hpath hregular position
      rw [← hother]
      simpa [otherPosition, InternalPosition.nextVertex] using
        congrArg path.getVert heq
    exact ⟨⟨otherPosition, hother, hprevious, hnext⟩⟩
  · exact Or.inr hsupport

end Mettapedia.GraphTheory.CubicPathAttachment
