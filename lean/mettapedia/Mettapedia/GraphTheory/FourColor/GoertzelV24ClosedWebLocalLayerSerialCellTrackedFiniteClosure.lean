import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFullProfileRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphThreeFactorContraction

/-!
# Finite closure of one tracked source-Cell transition

The accumulated prefix, the literal Cell, and their residual seam are the
three graph factors in one source-faithful connectivity update.  The preceding
files put the two local factors on one carrier of at most twenty-one edges and
encode the prefix's complete component attachments on the same stable slots.

This file closes that tracked coordinate junction.  First it proves that all
switches among the three literal factors occur on the common finite carrier.
It then transports their three-factor component closure to the carrier code.
Thus the complete pre-rebase tracked reachability relation is computed from
the incoming bounded profile, its finite prefix-attachment state, and the two
finite local factor graphs.

This is only the tracked-connectivity coordinate of one heterogeneous source
letter.  The facial attachment/cap coordinate and the theorem assembling all
five profile fields remain separate obligations; no full transfer relation or
usable base threshold is claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceSpliceConnectivity
open GoertzelV24SimpleGraphThreeFactorContraction
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The code coordinate embedded in the fixed twenty-one-slot prefix state. -/
def sourceLocalLayerSerialTrackedFiniteStableSlot
    (code : BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool)) :
    Fin code.vertexCount.val → Fin 21 :=
  fun coordinate => Fin.castLE (Nat.le_of_lt_succ code.vertexCount.isLt)
    coordinate

/-- One of the two literal outgoing crossings, retained as a point of the
common transition carrier. -/
noncomputable def sourceLocalLayerSerialTrackedOutgoingCarrierPointAt
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    {edge // edge ∈ sourceLocalLayerSerialTrackedTransitionCarrierAt
      graphData caps coloring web corridor hunique offset} :=
  ⟨sourceLocalLayerRightCrossingAt corridor hunique offset step,
    Finset.mem_union_left _ (Finset.mem_union_left _
      (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
        step))⟩

/-- The graph-free one-Cell tracked step on the literal finite carrier.
The predecessor factor is reconstructed from finite attachments and the
incoming profile; the other two factors are the coded Cell and seam graphs. -/
def SourceLocalLayerSerialTrackedFiniteComponentStep
    (state : SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (code : BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) : Prop :=
  sourceLocalLayerSerialTrackedPrefixFactoredReachability state input pair
      (sourceLocalLayerSerialTrackedFiniteStableSlot code left)
      (sourceLocalLayerSerialTrackedFiniteStableSlot code right) ∨
    (code.graph (pair, false)).Reachable left right ∨
    (code.graph (pair, true)).Reachable left right

/-- Every nontrivial switch among prefix, Cell, and seam lies on the common
transition carrier.  Hence literal pre-rebase reachability is exactly the
three-factor closure on that selected carrier. -/
theorem sourceLocalLayerSerialPreRebaseTrackedReachable_iff_transitionCarrierClosure
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    (regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      coloring (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (SelectedThreeFactorComponentStep
          (regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
            coloring (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
          (regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset)
            coloring (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
          (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
            coloring (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
          (fun edge => edge ∈
            sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset))
        left right := by
  rw [sourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor corridor
    hunique offset coloring (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2]
  apply reachable_sup_sup_iff_subtype_threeFactorComponentClosure
  · intro x middle y hx hy hprefix hcell
    have hinter := regionalTrackedEdgeGraph_switch_mem_inter web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      (sourceLocalLayerCellRegionAt corridor hunique offset)
      coloring (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 hx hy hprefix hcell
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_inter.1 hinter).2)
  · intro x middle y _hx hy _hprefix hseam
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (sourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
        corridor hunique offset coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (SimpleGraph.mem_support_of_reachable hy hseam)))
  · intro x middle y _hx hy _hcell hseam
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (sourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
        corridor hunique offset coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (SimpleGraph.mem_support_of_reachable hy hseam)))

/-- Complete tracked reachability after adjoining one literal source Cell is
the closure of a graph-free relation on at most twenty-one coordinates.  Its
only predecessor inputs are the bounded incoming profile and the finite
attachment state extracted from that prefix. -/
theorem sourceLocalLayerSerialPreRebaseTrackedReachable_iff_finiteClosure
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    (regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      coloring (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialTrackedFiniteComponentStep
          (sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData caps
            coloring web corridor hunique offset)
          (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
            offset)
          (sourceLocalLayerSerialTrackedTransitionCodeAt graphData minimal caps
            coloring web corridor hunique offset)
          pair)
        (carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset) left)
        (carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset) right) := by
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialTrackedTransitionCodeAt graphData minimal
    caps coloring web corridor hunique offset
  let state := sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData
    caps coloring web corridor hunique offset
  let input := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
    hunique offset
  rw [sourceLocalLayerSerialPreRebaseTrackedReachable_iff_transitionCarrierClosure
    graphData caps coloring web corridor hunique offset pair left right]
  have hslot (edge : {edge // edge ∈ carrier}) :
      sourceLocalLayerSerialTrackedFiniteStableSlot code (coordinate edge) =
        sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge := by
    rfl
  have hstep (first second : {edge // edge ∈ carrier}) :
      SelectedThreeFactorComponentStep
          (regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
            coloring (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
          (regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset)
            coloring (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
          (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
            coloring (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
          (fun edge => edge ∈ carrier) first second ↔
        SourceLocalLayerSerialTrackedFiniteComponentStep state input code pair
          (coordinate first) (coordinate second) := by
    simp only [SelectedThreeFactorComponentStep,
      SourceLocalLayerSerialTrackedFiniteComponentStep]
    rw [hslot first, hslot second]
    constructor
    · rintro (hprefix | hcell | hseam)
      · exact Or.inl
          ((sourceLocalLayerSerialTrackedPrefixAttachmentStateAt_factoredReachability_iff
            graphData minimal caps coloring web corridor hunique offset pair
              first second).2 hprefix)
      · exact Or.inr (Or.inl
          ((sourceLocalLayerSerialTrackedTransitionCodeAt_cell_reachable_iff
            graphData minimal caps coloring web corridor hunique offset pair
              first second).2 hcell))
      · exact Or.inr (Or.inr
          ((sourceLocalLayerSerialTrackedTransitionCodeAt_seam_reachable_iff
            graphData minimal caps coloring web corridor hunique offset pair
              first second).2 hseam))
    · rintro (hprefix | hcell | hseam)
      · exact Or.inl
          ((sourceLocalLayerSerialTrackedPrefixAttachmentStateAt_factoredReachability_iff
            graphData minimal caps coloring web corridor hunique offset pair
              first second).1 hprefix)
      · exact Or.inr (Or.inl
          ((sourceLocalLayerSerialTrackedTransitionCodeAt_cell_reachable_iff
            graphData minimal caps coloring web corridor hunique offset pair
              first second).1 hcell))
      · exact Or.inr (Or.inr
          ((sourceLocalLayerSerialTrackedTransitionCodeAt_seam_reachable_iff
            graphData minimal caps coloring web corridor hunique offset pair
              first second).1 hseam))
  constructor
  · intro hclosure
    exact Relation.ReflTransGen.lift coordinate
      (fun first second h => (hstep first second).1 h) hclosure
  · intro hclosure
    have hlift := Relation.ReflTransGen.lift coordinate.symm
      (fun first second h =>
        (hstep (coordinate.symm first) (coordinate.symm second)).2 (by
          simpa using h)) hclosure
    simpa [coordinate, carrier] using hlift

/-- The actual outgoing profile's tracked-connectivity field is exactly the
finite closure above, guarded by the two displayed output colours.  This is
the projection needed by a later full five-coordinate letter decoder. -/
theorem sourceLocalLayerSerialPreRebaseOutput_strandConnected_iff_finiteClosure
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (pair : TrackedColorPair)
    (left right : Fin 2) :
    (sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor hunique
        offset).profile.strandConnected pair (.inl left) (.inl right) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          ((sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor
            hunique offset).profile.edgeColor left).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          ((sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor
            hunique offset).profile.edgeColor right).toColor ∧
        Relation.ReflTransGen
          (SourceLocalLayerSerialTrackedFiniteComponentStep
            (sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData caps
              coloring web corridor hunique offset)
            (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
              hunique offset)
            (sourceLocalLayerSerialTrackedTransitionCodeAt graphData minimal caps
              coloring web corridor hunique offset)
            pair)
          (carrierCoordinate
            (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset)
            (sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData caps
              coloring web corridor hunique offset left))
          (carrierCoordinate
            (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset)
            (sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData caps
              coloring web corridor hunique offset right)) := by
  let relation := sourceLocalLayerSerialCellFullProfileRelation_of_ambientColoring
    corridor hunique offset
  rw [relation.outputStrandConnected pair left right,
    relation.outputEdgeColor left, relation.outputEdgeColor right]
  let leftPoint := sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData
    caps coloring web corridor hunique offset left
  let rightPoint := sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData
    caps coloring web corridor hunique offset right
  have hold := sourceLocalLayerSerialPreRebaseTrackedReachable_iff corridor
    hunique offset coloring (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2 leftPoint.1 rightPoint.1
  have hfinite := sourceLocalLayerSerialPreRebaseTrackedReachable_iff_finiteClosure
    graphData minimal caps coloring web corridor hunique offset pair leftPoint
      rightPoint
  exact and_congr_right fun _ =>
    and_congr_right fun _ => hold.symm.trans hfinite

end

end GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure

end Mettapedia.GraphTheory.FourColor
