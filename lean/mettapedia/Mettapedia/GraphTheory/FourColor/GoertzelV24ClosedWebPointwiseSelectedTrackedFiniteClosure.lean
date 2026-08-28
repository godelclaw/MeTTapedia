import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedPrefixAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFiniteTrackedColorCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure

/-!
# Finite tracked closure for a pointwise-selected Cell

An arbitrary terminal-aware cumulative prefix, a positive literal Cell, and
their residual seam are the three exact tracked factors of the selected
pre-rebase output.  The prefix is represented by its incoming profile and
finite attachment state; the two local factors are reconstructed from the
prefix and Cell colour tables on the fixed twenty-one-slot carrier.

This file proves exact soundness and completeness of that graph-free closure.
Only colours on the actual terminal overlap must agree.  No global
shared-interior-edge selector is used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceSpliceConnectivity
open GoertzelV24SimpleGraphThreeFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedTrackedFiniteClosureEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- One selected outgoing crossing as a point of the complete tracked
transition carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedOutgoingPointAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset} :=
  ⟨pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset step,
    Finset.mem_union_left _ (Finset.mem_union_left _
      (pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing formation
        corridor hinterior offset step))⟩

private theorem regionalTrackedEdgeGraph_eq_of_eq_on_region
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (RS : RotationSystem Vertex Edge) (region : Finset Edge)
    (leftColor rightColor : Edge → Color)
    (heq : ∀ edge, edge ∈ region → leftColor edge = rightColor edge)
    (first second : Color) :
    regionalTrackedEdgeGraph RS region leftColor first second =
      regionalTrackedEdgeGraph RS region rightColor first second := by
  ext left right
  simp only [regionalTrackedEdgeGraph, RotationSystem.trackedEdgeGraph]
  constructor
  · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
    exact ⟨⟨hadj, heq left hleft ▸ hleftTracked,
      heq right hright ▸ hrightTracked⟩, hleft, hright⟩
  · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
    exact ⟨⟨hadj, (heq left hleft).symm ▸ hleftTracked,
      (heq right hright).symm ▸ hrightTracked⟩, hleft, hright⟩

/-- Literal pre-rebase reachability is exactly the closure of prefix, Cell,
and residual seam on the selected common carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialPreRebaseTrackedReachableForColor_iff_transitionCarrierClosure
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset}) :
    (regionalTrackedEdgeGraph formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
        corridor hinterior offset) color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (SelectedThreeFactorComponentStep
          (regionalTrackedEdgeGraph formation.annular.RS
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              formation corridor hinterior offset) color
            (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)
          (regionalTrackedEdgeGraph formation.annular.RS
            (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
              hinterior offset) color (trackedColorPairColors pair).1
                (trackedColorPairColors pair).2)
          (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
            formation corridor hinterior offset color
              (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)
          (fun edge => edge ∈
            pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
              formation corridor hinterior offset)) left right := by
  rw [pointwiseSelectedSourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor
    formation corridor hinterior offset color (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2]
  apply reachable_sup_sup_iff_subtype_threeFactorComponentClosure
  · intro x middle y hx hy hprefix hcell
    have hinter := regionalTrackedEdgeGraph_switch_mem_inter
      formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
        corridor hinterior offset)
      (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset) color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 hx hy hprefix hcell
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_inter.1 hinter).2)
  · intro x middle y _hx hy _hprefix hseam
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
        formation corridor hinterior offset color
          (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
          (SimpleGraph.mem_support_of_reachable hy hseam)))
  · intro x middle y _hx hy _hcell hseam
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
        formation corridor hinterior offset color
          (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
          (SimpleGraph.mem_support_of_reachable hy hseam)))

/-- Exact finite tracked closure for a compatible arbitrary prefix and literal
Cell colour function.  The local transition graph is reconstructed solely
from the uncoloured carrier and the two finite colour tables. -/
theorem pointwiseSelectedSourceLocalLayerSerialPreRebaseTrackedReachableForCompatibleColors_iff_finiteClosure
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor cellColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        web.toFormation corridor hinterior offset prefixColor cellColor)
    (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    let spliced := pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
      web.toFormation corridor hinterior offset prefixColor cellColor
    let input :=
      pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
        web.toFormation corridor hinterior offset prefixColor hprefix
    let state :=
      pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
        web corridor hinterior offset prefixColor
    let code := pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors
      (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web corridor
        hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior offset) prefixColor)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) cellColor)
    (regionalTrackedEdgeGraph web.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
        web.toFormation corridor hinterior offset) spliced
        (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialTrackedFiniteComponentStep state input code pair)
        (carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
            web.toFormation corridor hinterior offset) left)
        (carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
            web.toFormation corridor hinterior offset) right) := by
  dsimp only
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior offset
  let coordinate := carrierCoordinate carrier
  let spliced := pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
    web.toFormation corridor hinterior offset prefixColor cellColor
  let input :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
      web.toFormation corridor hinterior offset prefixColor hprefix
  let state :=
    pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
      web corridor hinterior offset prefixColor
  let code := pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors
    (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web corridor
      hinterior offset hcell)
    (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
      corridor hinterior offset
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior offset) prefixColor)
    (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
      corridor hinterior offset
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset) cellColor)
  rw [pointwiseSelectedSourceLocalLayerSerialPreRebaseTrackedReachableForColor_iff_transitionCarrierClosure
    web.toFormation corridor hinterior offset spliced pair left right]
  have hprefixGraph :
      regionalTrackedEdgeGraph web.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            web.toFormation corridor hinterior offset) spliced
          (trackedColorPairColors pair).1 (trackedColorPairColors pair).2 =
        regionalTrackedEdgeGraph web.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            web.toFormation corridor hinterior offset) prefixColor
          (trackedColorPairColors pair).1 (trackedColorPairColors pair).2 := by
    apply regionalTrackedEdgeGraph_eq_of_eq_on_region
    intro edge hedge
    exact
      pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem_terminalInput
        web.toFormation corridor hinterior offset prefixColor cellColor
          hcompatible hedge
  have hslot (edge : {edge // edge ∈ carrier}) :
      sourceLocalLayerSerialTrackedFiniteStableSlot code (coordinate edge) =
        pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
          corridor hinterior offset hcell edge := by
    rfl
  have hstep (first second : {edge // edge ∈ carrier}) :
      SelectedThreeFactorComponentStep
          (regionalTrackedEdgeGraph web.annular.RS
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior offset) spliced
            (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)
          (regionalTrackedEdgeGraph web.annular.RS
            (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
              corridor hinterior offset) spliced
            (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)
          (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
            web.toFormation corridor hinterior offset spliced
            (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)
          (fun edge => edge ∈ carrier) first second ↔
        SourceLocalLayerSerialTrackedFiniteComponentStep state input code pair
          (coordinate first) (coordinate second) := by
    simp only [SelectedThreeFactorComponentStep,
      SourceLocalLayerSerialTrackedFiniteComponentStep]
    rw [hslot first, hslot second]
    constructor
    · rintro (hprefixStep | hcellStep | hseamStep)
      · exact Or.inl
          ((pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt_factoredReachability_iff
            web corridor hinterior offset hcell prefixColor hprefix pair first
              second).2 (by simpa [hprefixGraph] using hprefixStep))
      · exact Or.inr (Or.inl
          ((pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_reachable_iff
            web corridor hinterior offset hcell prefixColor cellColor
              (pair, false) (coordinate first) (coordinate second)).2
            ((pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt_cell_reachable_iff
              web corridor hinterior offset hcell spliced pair first second).2
                hcellStep)))
      · exact Or.inr (Or.inr
          ((pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_reachable_iff
            web corridor hinterior offset hcell prefixColor cellColor
              (pair, true) (coordinate first) (coordinate second)).2
            ((pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt_seam_reachable_iff
              web corridor hinterior offset hcell spliced pair first second).2
                hseamStep)))
    · rintro (hprefixStep | hcellStep | hseamStep)
      · have hactual :=
          (pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt_factoredReachability_iff
            web corridor hinterior offset hcell prefixColor hprefix pair first
              second).1 hprefixStep
        exact Or.inl (by simpa [hprefixGraph] using hactual)
      · exact Or.inr (Or.inl
          ((pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt_cell_reachable_iff
            web corridor hinterior offset hcell spliced pair first second).1
            ((pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_reachable_iff
              web corridor hinterior offset hcell prefixColor cellColor
                (pair, false) (coordinate first) (coordinate second)).1
                  hcellStep)))
      · exact Or.inr (Or.inr
          ((pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt_seam_reachable_iff
            web corridor hinterior offset hcell spliced pair first second).1
            ((pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_reachable_iff
              web corridor hinterior offset hcell prefixColor cellColor
                (pair, true) (coordinate first) (coordinate second)).1
                  hseamStep)))
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

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
