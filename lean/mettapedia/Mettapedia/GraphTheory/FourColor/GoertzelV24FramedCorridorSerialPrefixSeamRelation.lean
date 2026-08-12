import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicEdgeAdjacencyNeighborhood
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixSeamSupport

/-!
# Outgoing-indexed relations for a source serial-prefix seam

The residual seam between the genuine open prefix and one literal Cell is
not an arbitrary third graph.  Every seam adjacency joins an edge belonging
only to the old prefix to one of the Cell's two outgoing crossings.  This
file records that statement as an exact relation, for both tracked
connectivity and occurrence-sensitive facial continuation.

The outgoing coordinate is finite (`Fin 2`), but the old-prefix endpoint is
deliberately retained.  Thus these relations do not yet assert that the
current finite profile determines the seam, or that colour-word agreement is
full profile agreement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileRegionalCoverage
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixSeamRelationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- One oriented tracked residual turn: an old-prefix-only edge is adjacent
to a Cell-only edge at a specified outgoing crossing. -/
def SourceCorridorSerialInputTrackedOutgoingSeamTurnAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color)
    (step : Fin 2) (oldEdge outputEdge : G.edgeSet) : Prop :=
  outputEdge =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing step ∧
    (embedded.cellulation.rotation.toRotationSystem.trackedEdgeGraph
      color first second).Adj oldEdge outputEdge ∧
    oldEdge ∈ sourceCorridorSerialCutRegionAt realization hcubic hrotation
      htwoSided hunique offset ∧
    oldEdge ∉ sourceSlabLiteralCellRegionAt realization hcubic hrotation
      htwoSided hunique offset ∧
    outputEdge ∈ sourceSlabLiteralCellRegionAt realization hcubic hrotation
      htwoSided hunique offset ∧
    outputEdge ∉ sourceCorridorSerialCutRegionAt realization hcubic
      hrotation htwoSided hunique offset

/-- Exact outgoing-indexed form of every tracked residual adjacency. -/
theorem sourceCorridorSerialInputTrackedSeamGraphAt_adj_iff_exists_outgoingTurn
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) (x y : G.edgeSet) :
    (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic hrotation
      htwoSided hunique offset color first second).Adj x y ↔
      ∃ step : Fin 2,
        SourceCorridorSerialInputTrackedOutgoingSeamTurnAt realization hcubic
            hrotation htwoSided hunique offset color first second step x y ∨
          SourceCorridorSerialInputTrackedOutgoingSeamTurnAt realization hcubic
            hrotation htwoSided hunique offset color first second step y x := by
  let leftRegion := sourceCorridorSerialCutRegionAt realization hcubic
    hrotation htwoSided hunique offset
  let cellRegion := sourceSlabLiteralCellRegionAt realization hcubic hrotation
    htwoSided hunique offset
  constructor
  · intro hadj
    have hraw := (regionalTrackedSeamGraph_adj_iff
      embedded.cellulation.rotation.toRotationSystem leftRegion cellRegion
      color first second x y).1 (by
        simpa [sourceCorridorSerialInputTrackedSeamGraphAt, leftRegion,
          cellRegion] using hadj)
    rcases hraw with ⟨htracked, hforward | hbackward⟩
    · rcases sourceCorridorSerialInputTrackedSeamGraphAt_adj_touches_outputCrossing
        realization hcubic hrotation htwoSided hunique offset color first second
        hadj with ⟨step, hxOutput | hyOutput⟩
      · have hxCell : x ∈ cellRegion := by
          simpa [cellRegion, hxOutput] using
            sourceSlabLiteralCellRegionAt_rightCrossing realization hcubic
              hrotation htwoSided hunique offset step
        exact (hforward.2.1 hxCell).elim
      · refine ⟨step, Or.inl ?_⟩
        exact ⟨hyOutput, htracked, hforward.1, hforward.2.1,
          hforward.2.2.1, hforward.2.2.2⟩
    · rcases sourceCorridorSerialInputTrackedSeamGraphAt_adj_touches_outputCrossing
        realization hcubic hrotation htwoSided hunique offset color first second
        hadj with ⟨step, hxOutput | hyOutput⟩
      · refine ⟨step, Or.inr ?_⟩
        exact ⟨hxOutput, htracked.symm, hbackward.2.2.1,
          hbackward.2.2.2, hbackward.1, hbackward.2.1⟩
      · have hyCell : y ∈ cellRegion := by
          simpa [cellRegion, hyOutput] using
            sourceSlabLiteralCellRegionAt_rightCrossing realization hcubic
              hrotation htwoSided hunique offset step
        exact (hbackward.2.2.2 hyCell).elim
  · rintro ⟨step, hturn | hturn⟩
    · rcases hturn with
        ⟨_houtput, htracked, hxLeft, hxNotCell, hyCell, hyNotLeft⟩
      apply (regionalTrackedSeamGraph_adj_iff
        embedded.cellulation.rotation.toRotationSystem leftRegion cellRegion
        color first second x y).2
      exact ⟨htracked, Or.inl ⟨hxLeft, hxNotCell, hyCell, hyNotLeft⟩⟩
    · rcases hturn with
        ⟨_houtput, htracked, hyLeft, hyNotCell, hxCell, hxNotLeft⟩
      apply (regionalTrackedSeamGraph_adj_iff
        embedded.cellulation.rotation.toRotationSystem leftRegion cellRegion
        color first second x y).2
      exact ⟨htracked.symm, Or.inr ⟨hxCell, hxNotLeft, hyLeft, hyNotCell⟩⟩

/-- One oriented facial residual turn.  The two vertices remain actual
occurrences on the selected face cycle; only the Cell endpoint is compressed
to its outgoing `Fin 2` coordinate. -/
def SourceCorridorSerialInputFaceOutgoingSeamTurnAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (step : Fin 2)
    (oldPosition outputPosition : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :
    Prop :=
  faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
      outputPosition =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing step ∧
    (faceCyclePositionGraph embedded.cellulation.rotation.toRotationSystem
      root).Adj oldPosition outputPosition ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        oldPosition ∈
      sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique offset ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        oldPosition ∉
      sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique offset ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        outputPosition ∈
      sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique offset ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        outputPosition ∉
      sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique offset

/-- Exact outgoing-indexed form of every occurrence-sensitive facial seam
adjacency. -/
theorem sourceCorridorSerialInputFaceSeamGraphAt_adj_iff_exists_outgoingTurn
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :
    (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic hrotation
      htwoSided hunique offset root).Adj x y ↔
      ∃ step : Fin 2,
        SourceCorridorSerialInputFaceOutgoingSeamTurnAt realization hcubic
            hrotation htwoSided hunique offset root step x y ∨
          SourceCorridorSerialInputFaceOutgoingSeamTurnAt realization hcubic
            hrotation htwoSided hunique offset root step y x := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let leftRegion := sourceCorridorSerialCutRegionAt realization hcubic
    hrotation htwoSided hunique offset
  let cellRegion := sourceSlabLiteralCellRegionAt realization hcubic hrotation
    htwoSided hunique offset
  constructor
  · intro hadj
    have hraw := (faceRegionalSeamGraph_adj_iff RS root leftRegion cellRegion
      x y).1 (by
        simpa [sourceCorridorSerialInputFaceSeamGraphAt, RS, leftRegion,
          cellRegion] using hadj)
    rcases hraw with ⟨hface, hforward | hbackward⟩
    · rcases sourceCorridorSerialInputFaceSeamGraphAt_adj_touches_outputCrossing
        realization hcubic hrotation htwoSided hunique offset root hadj with
        ⟨step, hxOutput | hyOutput⟩
      · have hxCell : faceCycleEdge RS root x ∈ cellRegion := by
          simpa [RS, cellRegion, hxOutput] using
            sourceSlabLiteralCellRegionAt_rightCrossing realization hcubic
              hrotation htwoSided hunique offset step
        exact (hforward.2.1 hxCell).elim
      · refine ⟨step, Or.inl ?_⟩
        exact ⟨hyOutput, hface, hforward.1, hforward.2.1,
          hforward.2.2.1, hforward.2.2.2⟩
    · rcases sourceCorridorSerialInputFaceSeamGraphAt_adj_touches_outputCrossing
        realization hcubic hrotation htwoSided hunique offset root hadj with
        ⟨step, hxOutput | hyOutput⟩
      · refine ⟨step, Or.inr ?_⟩
        exact ⟨hxOutput, hface.symm, hbackward.2.2.1,
          hbackward.2.2.2, hbackward.1, hbackward.2.1⟩
      · have hyCell : faceCycleEdge RS root y ∈ cellRegion := by
          simpa [RS, cellRegion, hyOutput] using
            sourceSlabLiteralCellRegionAt_rightCrossing realization hcubic
              hrotation htwoSided hunique offset step
        exact (hbackward.2.2.2 hyCell).elim
  · rintro ⟨step, hturn | hturn⟩
    · rcases hturn with
        ⟨_houtput, hface, hxLeft, hxNotCell, hyCell, hyNotLeft⟩
      apply (faceRegionalSeamGraph_adj_iff RS root leftRegion cellRegion
        x y).2
      exact ⟨hface, Or.inl ⟨hxLeft, hxNotCell, hyCell, hyNotLeft⟩⟩
    · rcases hturn with
        ⟨_houtput, hface, hyLeft, hyNotCell, hxCell, hxNotLeft⟩
      apply (faceRegionalSeamGraph_adj_iff RS root leftRegion cellRegion
        x y).2
      exact ⟨hface.symm, Or.inr ⟨hxCell, hxNotLeft, hyLeft, hyNotCell⟩⟩

/-- The two outgoing crossings together with all their adjacent ambient
edges.  This is a finite carrier for both species of residual seam turn. -/
noncomputable def sourceCorridorSerialOutgoingEdgeCarrierAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyClosedCarrier
    (indexedCrossingEdgeSet
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing))

/-- The residual carrier has a uniform graph-independent bound: two outgoing
edges, each with a closed cubic edge neighborhood of size at most seven. -/
theorem sourceCorridorSerialOutgoingEdgeCarrierAt_card_le_fourteen
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3)) :
    (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
      htwoSided hunique offset).card ≤ 14 := by
  let output :=
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing
  calc
    (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
      htwoSided hunique offset).card ≤
        7 * (indexedCrossingEdgeSet output).card := by
      exact embedded.cellulation.rotation.toRotationSystem
        |>.edgeAdjacencyClosedCarrier_card_le_seven_mul hcubic _
    _ ≤ 7 * 2 := Nat.mul_le_mul_left 7
      (card_indexedCrossingEdgeSet_le output)
    _ = 14 := by norm_num

/-- Every edge used by a tracked residual seam belongs to the bounded
outgoing-edge carrier. -/
theorem sourceCorridorSerialInputTrackedSeamGraphAt_support_subset_outgoingCarrier
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) :
    (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic hrotation
      htwoSided hunique offset color first second).support ⊆
      sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
        htwoSided hunique offset := by
  intro edge hedge
  rcases (SimpleGraph.mem_support
      (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic hrotation
        htwoSided hunique offset color first second)).1 hedge with
    ⟨neighbor, hadj⟩
  rcases sourceCorridorSerialInputTrackedSeamGraphAt_adj_iff_exists_outgoingTurn
      realization hcubic hrotation htwoSided hunique offset color first second
      edge neighbor |>.1 hadj with ⟨step, hforward | hbackward⟩
  · apply (embedded.cellulation.rotation.toRotationSystem
      |>.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
    exact Or.inr ⟨_,
      (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, hforward.1.symm⟩,
      hforward.2.1.1⟩
  · apply (embedded.cellulation.rotation.toRotationSystem
      |>.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
    exact Or.inl
      ((mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, hbackward.1.symm⟩)

/-- Every face occurrence used by a facial residual projects to the same
bounded outgoing-edge carrier. -/
theorem sourceCorridorSerialInputFaceSeamGraphAt_support_projects_outgoingCarrier
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    ∀ position ∈
      (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic hrotation
        htwoSided hunique offset root).support,
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
          position ∈
        sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
          htwoSided hunique offset := by
  intro position hposition
  rcases (SimpleGraph.mem_support
      (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic hrotation
        htwoSided hunique offset root)).1 hposition with
    ⟨neighbor, hadj⟩
  rcases sourceCorridorSerialInputFaceSeamGraphAt_adj_iff_exists_outgoingTurn
      realization hcubic hrotation htwoSided hunique offset root
      position neighbor |>.1 hadj with ⟨step, hforward | hbackward⟩
  · apply (embedded.cellulation.rotation.toRotationSystem
      |>.mem_edgeAdjacencyClosedCarrier_iff _ _).2
    refine Or.inr ⟨_,
      (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, hforward.1.symm⟩, ?_⟩
    exact edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
      embedded.cellulation.rotation.toRotationSystem hcubic hrotation root
      hforward.2.1
  · apply (embedded.cellulation.rotation.toRotationSystem
      |>.mem_edgeAdjacencyClosedCarrier_iff _ _).2
    exact Or.inl
      ((mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, hbackward.1.symm⟩)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
