import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCap
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCap
import Mettapedia.GraphTheory.FourColor.ExactSizedCyclicEdgeCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCapGeometry

/-!
# Instantiating the five-cut caps at an exact cyclic five-edge cut

A cyclic boundary order of the retained shore enumerates the five cut
edges.  Reading the crossing edges off the order yields the data of the
pentagon cap and of the Y-cap: the shore Finset is the complement cut
side, the ordered cut is the shore's literal edge boundary, and the
order itself is recovered as the cap's crossing boundary-dart
enumeration.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace FiveCutCapAssembly

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutCapGeometry
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The retained shore of an exact cut, as the membership predicate of the
complement cut side.  This is definitionally the `keep` predicate of every
cap built on this shore. -/
def shoreKeep (cut : ExactSizedCyclicEdgeCut G 5) : V → Prop :=
  fun vertex => vertex ∈ exactCutVertexSide cut.compl

/-- The shore keep predicate is the canonical deleted-region keep. -/
theorem shoreKeep_eq_deletedRegionKeep (cut : ExactSizedCyclicEdgeCut G 5) :
    shoreKeep cut = deletedRegionKeep (exactCutVertexSide cut) := by
  funext vertex
  apply propext
  rw [shoreKeep, mem_exactCutVertexSide_iff, deletedRegionKeep,
    mem_exactCutVertexSide_iff]
  exact Iff.rfl

variable (graphData : Data G) (cut : ExactSizedCyclicEdgeCut G 5)

/-- The crossing edges read off a boundary order of the shore. -/
def crossingOfOrder
    (capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut)) : Fin 5 → G.edgeSet :=
  fun step => graphData.toRotationSystem.edgeOf (capOrder step).1.1

theorem crossingOfOrder_injective
    (capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut)) :
    Function.Injective (crossingOfOrder graphData cut capOrder) := by
  intro first second hedge
  apply capOrder.injective
  exact boundaryDart_eq_of_edgeOf_eq graphData.toRotationSystem
    (shoreKeep cut) (capOrder first) (capOrder second) hedge

/-- Each ordered crossing edge lies in the ambient cut. -/
theorem crossingOfOrder_mem_edgeCut
    (capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut)) (step : Fin 5) :
    crossingOfOrder graphData cut capOrder step ∈ cut.edgeCut := by
  show crossingOfOrder graphData cut capOrder step ∈ cut.compl.edgeCut
  rw [← vertexSetCrossingEdges_exactCutVertexSide graphData cut.compl]
  rw [mem_vertexSetCrossingEdges_iff]
  refine ⟨graphData.toRotationSystem.vertOf (capOrder step).1.1, ?_, ?_,
    graphData.toRotationSystem.vertOf
      (graphData.toRotationSystem.alpha (capOrder step).1.1), ?_, ?_⟩
  · exact (graphData.toRotationSystem.mem_endpoints_iff).2
      ⟨(capOrder step).1.1,
        (graphData.toRotationSystem.mem_dartsOn).2 rfl, rfl⟩
  · exact (capOrder step).1.2
  · exact (graphData.toRotationSystem.mem_endpoints_iff).2
      ⟨graphData.toRotationSystem.alpha (capOrder step).1.1, by
        rw [graphData.toRotationSystem.mem_dartsOn]
        exact graphData.toRotationSystem.edge_alpha _, rfl⟩
  · exact (capOrder step).2

/-- The shore's literal edge boundary is the ordered cut of the order's
crossing edges. -/
theorem boundary_eq_orderedCut_crossingOfOrder
    (capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut)) :
    graphData.toRotationSystem.vertexSideEdgeBoundary
        (exactCutVertexSide cut.compl) =
      orderedCut (crossingOfOrder graphData cut capOrder) := by
  have hboundary :
      graphData.toRotationSystem.vertexSideEdgeBoundary
          (exactCutVertexSide cut.compl) = cut.edgeCut := by
    rw [← vertexSetCrossingEdges_eq_vertexSideEdgeBoundary,
      vertexSetCrossingEdges_exactCutVertexSide graphData cut.compl]
    rfl
  rw [hboundary]
  have hsubset : orderedCut (crossingOfOrder graphData cut capOrder) ⊆
      cut.edgeCut := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with ⟨step, _, hstep⟩
    rw [← hstep]
    exact crossingOfOrder_mem_edgeCut graphData cut capOrder step
  have hcard : cut.edgeCut.card ≤
      (orderedCut (crossingOfOrder graphData cut capOrder)).card := by
    rw [cut.hcard_eq, orderedCut,
      Finset.card_image_of_injective _
        (crossingOfOrder_injective graphData cut capOrder)]
    simp
  exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

/-- The pentagon cap of the shore, at a chosen boundary order and anchored
retained dart. -/
def pentagonCapDataOfOrder
    (capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut))
    (anchor : graphData.toRotationSystem.D)
    (hanchor : shoreKeep cut
      (graphData.toRotationSystem.vertOf anchor)) :
    FiveEdgeCutPentagonCapData graphData.toRotationSystem where
  side := exactCutVertexSide cut.compl
  crossing := crossingOfOrder graphData cut capOrder
  crossing_injective := crossingOfOrder_injective graphData cut capOrder
  boundary_eq := boundary_eq_orderedCut_crossingOfOrder graphData cut capOrder
  anchor := anchor
  anchor_mem := hanchor

/-- The Y-cap of the shore, at a chosen boundary order, anchored retained
dart, and seam-distinctness certificate. -/
def yCapDataOfOrder
    (capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut))
    (anchor : graphData.toRotationSystem.D)
    (hanchor : shoreKeep cut
      (graphData.toRotationSystem.vertOf anchor))
    (hseam : graphData.toRotationSystem.vertOf (capOrder 0).1.1 ≠
      graphData.toRotationSystem.vertOf (capOrder 1).1.1) :
    FiveEdgeCutYCapData graphData.toRotationSystem where
  side := exactCutVertexSide cut.compl
  crossing := crossingOfOrder graphData cut capOrder
  crossing_injective := crossingOfOrder_injective graphData cut capOrder
  boundary_eq := boundary_eq_orderedCut_crossingOfOrder graphData cut capOrder
  anchor := anchor
  anchor_mem := hanchor
  seamEndpointsDistinct := by
    intro left right hleft hright
    have hleftEq : left = capOrder 0 :=
      boundaryDart_eq_of_edgeOf_eq graphData.toRotationSystem _ left
        (capOrder 0) hleft
    have hrightEq : right = capOrder 1 :=
      boundaryDart_eq_of_edgeOf_eq graphData.toRotationSystem _ right
        (capOrder 1) hright
    rw [hleftEq, hrightEq]
    exact hseam

/-- The pentagon cap's crossing enumeration recovers the boundary order. -/
theorem crossingBoundaryDartEquiv_pentagonCapDataOfOrder
    (capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut))
    (anchor : graphData.toRotationSystem.D)
    (hanchor : shoreKeep cut
      (graphData.toRotationSystem.vertOf anchor)) :
    (pentagonCapDataOfOrder graphData cut capOrder anchor
        hanchor).crossingBoundaryDartEquiv = capOrder := by
  apply Equiv.ext
  intro step
  apply boundaryDart_eq_of_edgeOf_eq graphData.toRotationSystem
  rw [(pentagonCapDataOfOrder graphData cut capOrder anchor
    hanchor).crossingBoundaryDartEquiv_edgeOf step]
  rfl

/-- The Y-cap's crossing enumeration recovers the boundary order. -/
theorem crossingBoundaryDartEquiv_yCapDataOfOrder
    (capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut))
    (anchor : graphData.toRotationSystem.D)
    (hanchor : shoreKeep cut
      (graphData.toRotationSystem.vertOf anchor))
    (hseam : graphData.toRotationSystem.vertOf (capOrder 0).1.1 ≠
      graphData.toRotationSystem.vertOf (capOrder 1).1.1) :
    (yCapDataOfOrder graphData cut capOrder anchor hanchor
        hseam).crossingBoundaryDartEquiv = capOrder := by
  apply Equiv.ext
  intro step
  apply boundaryDart_eq_of_edgeOf_eq graphData.toRotationSystem
  rw [(yCapDataOfOrder graphData cut capOrder anchor hanchor
    hseam).crossingBoundaryDartEquiv_edgeOf step]
  rfl

end

end FiveCutCapAssembly

end Mettapedia.GraphTheory.FourColor
