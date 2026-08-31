import Mettapedia.GraphTheory.FiniteBoundaryConnectivityState
import Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathConnectivity

/-!
# A fixed finite connectivity state for deletion paths

The physical boundary of a nine-deletion footprint has at most ninety
vertices, but its subtype depends on the ambient graph.  This file gives it a
fixed ninety-slot presentation.  Every site contributes two slots for its
central edge and two slots for each of its four boundary edges.  Slots may
coincide physically; this is intentional and is recorded by the connectivity
state itself.

The resulting state is a simple graph on one fixed finite type.  Its
reachability relation is exactly ambient reachability between the represented
vertices, and there are at most `2^(90*90)` such labelled states.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathConnectivityState

open AlternatingComponentLocalization
open DeletionPathConnectivity
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two central-edge endpoints, or two endpoints for one of four boundary
edges. -/
abbrev DeletionBoundarySlot := Fin 2 ⊕ (Fin 4 × Fin 2)

/-- Ten endpoint slots at each of nine deletion sites. -/
abbrev PathBoundarySlot := Fin 9 × DeletionBoundarySlot

theorem card_pathBoundarySlot : Fintype.card PathBoundarySlot = 90 := by
  decide

/-- The physical vertex named by one local endpoint slot. -/
def deletionBoundaryVertex
    (data : AdjacentPairData G) : DeletionBoundarySlot → V
  | Sum.inl side =>
      if side = 0 then data.firstVertex else data.secondVertex
  | Sum.inr (port, side) =>
      if side = 0 then boundaryDeletedVertex data port else data.portVertex port

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem deletionBoundaryVertex_central_zero (data : AdjacentPairData G) :
    deletionBoundaryVertex data (Sum.inl 0) = data.firstVertex := by
  simp [deletionBoundaryVertex]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem deletionBoundaryVertex_central_one (data : AdjacentPairData G) :
    deletionBoundaryVertex data (Sum.inl 1) = data.secondVertex := by
  simp [deletionBoundaryVertex]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem deletionBoundaryVertex_boundary_zero
    (data : AdjacentPairData G) (port : Fin 4) :
    deletionBoundaryVertex data (Sum.inr (port, 0)) =
      boundaryDeletedVertex data port := by
  simp [deletionBoundaryVertex]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem deletionBoundaryVertex_boundary_one
    (data : AdjacentPairData G) (port : Fin 4) :
    deletionBoundaryVertex data (Sum.inr (port, 1)) =
      data.portVertex port := by
  simp [deletionBoundaryVertex]

/-- The ambient vertex named by one of the fixed ninety path slots. -/
def pathBoundaryVertex
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (slot : PathBoundarySlot) : V :=
  deletionBoundaryVertex (family.data slot.1) slot.2

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every fixed slot names a vertex incident with the path footprint. -/
theorem pathBoundaryVertex_mem
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (slot : PathBoundarySlot) :
    pathBoundaryVertex family slot ∈ pathBoundaryVertices family := by
  rcases slot with ⟨index, endpointSlot⟩
  apply (SimpleGraph.mem_edgeBoundaryVertices _ _).2
  rcases endpointSlot with side | ⟨port, side⟩
  · refine ⟨centralEdgeValue (family.data index), ?_, ?_⟩
    · exact Finset.mem_image.2
        ⟨centralEdge (family.data index),
          Finset.mem_biUnion.2
            ⟨index, Finset.mem_univ _, by simp [deletionFootprint]⟩,
          rfl⟩
    · fin_cases side <;>
        simp [pathBoundaryVertex, deletionBoundaryVertex,
          centralEdgeValue, Sym2.mem_iff]
  · refine ⟨boundaryEdgeValue (family.data index) port, ?_, ?_⟩
    · exact Finset.mem_image.2
        ⟨boundaryEdge (family.data index) port,
          Finset.mem_biUnion.2
            ⟨index, Finset.mem_univ _, by
              simp [deletionFootprint]⟩,
          rfl⟩
    · fin_cases side <;>
        simp [pathBoundaryVertex, deletionBoundaryVertex,
          boundaryEdgeValue_eq, Sym2.mem_iff]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every physical boundary vertex has at least one of the fixed ninety
names. -/
theorem exists_pathBoundarySlot
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    {vertex : V} (hvertex : vertex ∈ pathBoundaryVertices family) :
    ∃ slot : PathBoundarySlot, pathBoundaryVertex family slot = vertex := by
  rcases (SimpleGraph.mem_edgeBoundaryVertices _ _).1 hvertex with
    ⟨edgeValue, hedgeValue, hvertexEdge⟩
  rcases Finset.mem_image.1 hedgeValue with
    ⟨edge, hedgePath, hedgeValueEq⟩
  rcases Finset.mem_biUnion.1 hedgePath with
    ⟨index, _, hedgeDeletion⟩
  simp only [deletionFootprint, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and] at hedgeDeletion
  rcases hedgeDeletion with hcentral | ⟨port, hboundary⟩
  · have hedge : edgeValue = centralEdgeValue (family.data index) := by
      calc
        edgeValue = edge.1 := hedgeValueEq.symm
        _ = (centralEdge (family.data index)).1 :=
          congrArg Subtype.val hcentral
        _ = centralEdgeValue (family.data index) := rfl
    have hendpoint : vertex = (family.data index).firstVertex ∨
        vertex = (family.data index).secondVertex := by
      rw [hedge, centralEdgeValue, Sym2.mem_iff] at hvertexEdge
      exact hvertexEdge
    rcases hendpoint with rfl | rfl
    · exact ⟨⟨index, Sum.inl 0⟩, by
        simp [pathBoundaryVertex]⟩
    · exact ⟨⟨index, Sum.inl 1⟩, by
        simp [pathBoundaryVertex]⟩
  · have hedge : edgeValue = boundaryEdgeValue (family.data index) port := by
      calc
        edgeValue = edge.1 := hedgeValueEq.symm
        _ = (boundaryEdge (family.data index) port).1 :=
          congrArg Subtype.val hboundary.symm
        _ = boundaryEdgeValue (family.data index) port := rfl
    have hendpoint : vertex = boundaryDeletedVertex (family.data index) port ∨
        vertex = (family.data index).portVertex port := by
      rw [hedge, boundaryEdgeValue_eq, Sym2.mem_iff] at hvertexEdge
      exact hvertexEdge
    rcases hendpoint with rfl | rfl
    · exact ⟨⟨index, Sum.inr (port, 0)⟩, by
        simp [pathBoundaryVertex]⟩
    · exact ⟨⟨index, Sum.inr (port, 1)⟩, by
        simp [pathBoundaryVertex]⟩

/-- A fixed-carrier encoding of component membership for one path graph. -/
def pathConnectivityState
    (graph : SimpleGraph V)
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) :
    SimpleGraph PathBoundarySlot :=
  SimpleGraph.boundaryConnectivityState graph (pathBoundaryVertex family)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The fixed state is extensionally exact: its connected components are the
ambient components of the represented physical vertices. -/
theorem pathConnectivityState_reachable_iff
    (graph : SimpleGraph V)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (left right : PathBoundarySlot) :
    (pathConnectivityState graph family).Reachable left right ↔
      graph.Reachable
        (pathBoundaryVertex family left) (pathBoundaryVertex family right) :=
  SimpleGraph.boundaryConnectivityState_reachable_iff _ _ _ _

/-- A coarse explicit bound on the number of normalized connectivity states
for a nine-deletion path. -/
theorem card_pathConnectivityState_le :
    Fintype.card (SimpleGraph PathBoundarySlot) ≤ 2 ^ (90 * 90) := by
  simpa only [card_pathBoundarySlot] using
    (SimpleGraph.card_simpleGraph_le_two_pow_sq (Port := PathBoundarySlot))

end

end Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathConnectivityState
