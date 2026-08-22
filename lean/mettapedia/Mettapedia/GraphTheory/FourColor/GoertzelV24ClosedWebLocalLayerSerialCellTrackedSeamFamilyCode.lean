import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPortalCompleteness
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicEdgeAdjacencyNeighborhood
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCounts
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpace

/-!
# A finite common carrier for one opened-source tracked Cell seam

The exact cumulative-prefix factorization leaves a residual tracked seam at
each literal source Cell.  Portal completeness proves that every residual
adjacency touches one of the Cell's two outgoing crossings.  This module
closes those two crossings under edge adjacency and transports all three
tracked-color seam graphs to the resulting common carrier.

The carrier has at most fourteen edges.  Unlike the older closed-map version,
the proof does not assume global cubicity: the annular stubs have degree one
and every other vertex has degree three, so the graph-backed rotation is
uniformly subcubic.

This is the exact finite connectivity residue used by one source Cell.  It
does not yet finite-code the occurrence-sensitive facial residue, nor claim
that the five-field one-Cell relation is independent of its literal slab.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedBoundaryCounts
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellTrackedSeamFamilyCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The graph-backed rotation and graph-level incident-edge finsets agree. -/
private theorem annularRS_incidentEdges_eq_incidentEdgeFinset
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (vertex : V) :
    web.annular.RS.incidentEdges vertex = incidentEdgeFinset G vertex := by
  ext edge
  rw [mem_toRotationSystem_incidentEdges_iff]
  simp [incidentEdgeFinset]

/-- An opened closed-web carrier is subcubic: its ten boundary stubs have
degree one and every other vertex has degree three. -/
theorem annularRS_incidentEdges_card_le_three
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (vertex : V) :
    (web.annular.RS.incidentEdges vertex).card ≤ 3 := by
  rw [annularRS_incidentEdges_eq_incidentEdgeFinset web vertex]
  by_cases hinner : ∃ inner : Fin 5, vertex = data.innerStub inner
  · rcases hinner with ⟨inner, rfl⟩
    rw [web.boundary_wellFormed.inner_stub_degree_one]
    omega
  · by_cases houter : ∃ outer : Fin 5, vertex = data.outerStub outer
    · rcases houter with ⟨outer, rfl⟩
      rw [web.boundary_wellFormed.outer_stub_degree_one]
      omega
    · rw [web.boundary_wellFormed.cubic_elsewhere vertex
          (fun inner heq => hinner ⟨inner, heq⟩)
          (fun outer heq => houter ⟨outer, heq⟩)]

/-- The common carrier is the two outgoing crossings together with every
ambient edge adjacent to either of them. -/
noncomputable def sourceLocalLayerSerialOutgoingEdgeCarrierAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  web.annular.RS.edgeAdjacencyClosedCarrier
    (indexedCrossingEdgeSet
      (sourceLocalLayerRightCrossingAt corridor hunique offset))

/-- Two outgoing crossings, each with a closed subcubic edge neighborhood of
size at most seven, give a carrier of size at most fourteen. -/
theorem sourceLocalLayerSerialOutgoingEdgeCarrierAt_card_le_fourteen
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset).card
      ≤ 14 := by
  calc
    (sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset).card
        ≤ 7 * (indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset)).card := by
      exact web.annular.RS
        |>.edgeAdjacencyClosedCarrier_card_le_seven_mul_of_incidentEdges_card_le_three
          (annularRS_incidentEdges_card_le_three web) _
    _ ≤ 7 * 2 := Nat.mul_le_mul_left 7
      (card_indexedCrossingEdgeSet_le
        (sourceLocalLayerRightCrossingAt corridor hunique offset))
    _ = 14 := by norm_num

/-- Every non-isolated edge of a literal tracked Cell seam belongs to the
common outgoing-edge carrier. -/
theorem sourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) :
    (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset color
      first second).support ⊆
      sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset := by
  intro edge hedge
  rcases (SimpleGraph.mem_support _).1 hedge with ⟨neighbor, hadj⟩
  have hambient : web.annular.RS.edgeAdjacencyGraph.Adj edge neighbor :=
    ((regionalTrackedSeamGraph_adj_iff web.annular.RS _ _ color first second
      edge neighbor).1 hadj).1.1
  rcases sourceLocalLayerSerialTerminalTrackedSeamAt_adj_touches_rightCrossing
      corridor hunique offset color first second hadj with
    ⟨step, hedgeRight | hneighborRight⟩
  · apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
    exact Or.inl ((mem_indexedCrossingEdgeSet_iff _ _).2
      ⟨step, hedgeRight.symm⟩)
  · apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
    exact Or.inr ⟨neighbor,
      (mem_indexedCrossingEdgeSet_iff _ _).2
        ⟨step, hneighborRight.symm⟩,
      hambient⟩

/-- One outgoing crossing retained as a named point of the common carrier,
including when it is isolated in one tracked-color seam. -/
noncomputable def sourceLocalLayerSerialOutgoingCrossingPointAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    {edge // edge ∈
      sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset} := by
  refine ⟨sourceLocalLayerRightCrossingAt corridor hunique offset step, ?_⟩
  apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
  exact Or.inl ((mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, rfl⟩)

/-- The three tracked-color residual graphs transported through one exact
finite carrier with the same two named outgoing coordinates. -/
noncomputable def sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color) :
    BoundedCarrierGraphFamilyCode 14 2 TrackedColorPair :=
  boundedCarrierGraphFamilyCode
    (sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset)
    14 2
    (sourceLocalLayerSerialOutgoingEdgeCarrierAt_card_le_fourteen corridor
      hunique offset)
    (sourceLocalLayerSerialOutgoingCrossingPointAt corridor hunique offset)
    (fun pair => sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique
      offset color (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2)

/-- The stored vertex count is the literal common-carrier cardinality. -/
theorem sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt_vertexCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color) :
    (sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt corridor hunique
      offset color).vertexCount.val =
      (sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset).card := by
  rfl

/-- The two outgoing coordinates remain distinct in the common code. -/
theorem sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt_point_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color) :
    Function.Injective
      (sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt corridor hunique
        offset color).point := by
  intro first second heq
  have hpoints :
      sourceLocalLayerSerialOutgoingCrossingPointAt corridor hunique offset first =
        sourceLocalLayerSerialOutgoingCrossingPointAt corridor hunique offset second := by
    apply (carrierCoordinate
      (sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset)).injective
    exact heq
  apply sourceLocalLayerRightCrossingAt_injective corridor hunique offset
  exact congrArg Subtype.val hpoints

/-- Every tracked adjacency on carrier edges is represented exactly. -/
theorem sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt_adj_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset}) :
    ((sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt corridor hunique
      offset color).graph pair).Adj
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Adj first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_adj_iff _ 14 2 _ _ _ pair first second

/-- The finite common code preserves ambient residual-seam reachability. -/
theorem sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset}) :
    ((sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt corridor hunique
      offset color).graph pair).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset)
    14 2
    (sourceLocalLayerSerialOutgoingEdgeCarrierAt_card_le_fourteen corridor
      hunique offset)
    (sourceLocalLayerSerialOutgoingCrossingPointAt corridor hunique offset)
    (fun tracked => sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique
      offset color (trackedColorPairColors tracked).1
        (trackedColorPairColors tracked).2)
    pair
    (sourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
      corridor hunique offset color (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2)
    first second

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
