import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceTransitionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFaceFixedState

/-!
# Finite predecessor facial attachments for a pointwise-selected Cell

The selected Cell and its residual seam live on the common twenty-four-dart
carrier.  This file records how the cumulative predecessor joins occurrences
on that carrier through its actual input boundary fragments.  It retains
regional presence and the cap at five of the distinct primal edges in each
predecessor face component, then pads the result to the fixed types `Fin 24`
and `Fin 4`.

All source geometry is pointwise-selected from interior-face uniqueness.  No
global shared-interior-edge selector occurs in the state or its adequacy
theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedTrail
open GoertzelV24HexCorridorSkeleton
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open Instance.LocalLayerFormation
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFacePrefixAttachmentStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- The actual occurrence-sensitive input boundary fragments used as ports of
the selected predecessor facial state. -/
abbrev PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :=
  BoundaryRegionalFragment formation.annular.RS
    (indexedCrossingEdgeSet
      (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset))
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset)

/-- A two-edge cut has at most four occurrence-sensitive predecessor
fragments, including on the opened one-sided carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceInputPortAt_card_le_four
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    Fintype.card
        (PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt formation
          corridor hinterior offset) ≤ 4 := by
  exact regionalBoundaryGraphCutData_fragmentCount_le_two_mul
    formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset)
    (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
      hinterior offset)

/-- Exact predecessor component attachments on the dependent selected
carrier and actual input-fragment ports. -/
abbrev PointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :=
  BoundedCappedSupportedPortResidualCode
    {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}
    (PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt formation corridor
      hinterior offset)

/-- Extract exact predecessor attachments, regional presence, and distinct
edge caps from the selected terminal-aware input region. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    PointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt formation
      corridor hinterior offset := by
  classical
  let region :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset
  let graph := faceRegionalDartGraph formation.annular.RS region
  let cut := indexedCrossingEdgeSet
    (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
      hinterior offset)
  let dartAt := fun dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset} => dart.1
  let portAt := fun port :
      PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt formation corridor
        hinterior offset =>
    (boundaryRegionalFragmentDartOccurrence formation.annular.RS cut region
      port).1
  exact {
    toBoundedSupportedPortResidualCode :=
      exactSupportedPortResidualCode graph dartAt portAt
    interfacePresent := fun dart =>
      decide (formation.annular.RS.edgeOf dart.1 ∈ region)
    componentCap := fun dart =>
      ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges
          formation.annular.RS region dart.1).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ }

/-- Canonical fixed slot of a selected transition-carrier dart. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset} → Fin 24 :=
  boundedFiniteSlot
    (by
      simpa [Fintype.card_subtype] using
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
          formation corridor hinterior offset hcell)

/-- Partial inverse of the fixed selected transition slot. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot?
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    Fin 24 → Option {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset} :=
  boundedFiniteSlot?
    (by
      simpa [Fintype.card_subtype] using
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
          formation corridor hinterior offset hcell)

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot?_slot
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot? formation
        corridor hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart) = some dart := by
  apply boundedFiniteSlot?_slot

/-- A live selected facial slot is uniquely the canonical slot of the dart it
decodes. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot?_eq_some_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (slot : Fin 24)
    (dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot? formation
        corridor hinterior offset hcell slot = some dart ↔
      slot =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart := by
  apply boundedFiniteSlot?_eq_some_iff

/-- Fixed slot of an actual selected predecessor fragment. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceInputPortSlotAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt formation corridor
      hinterior offset → Fin 4 :=
  boundedFiniteSlot
    (pointwiseSelectedSourceLocalLayerSerialFaceInputPortAt_card_le_four
      formation corridor hinterior offset)

/-- Partial decoder for fixed selected predecessor-fragment slots. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot?
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    Fin 4 → Option
      (PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt formation corridor
        hinterior offset) :=
  boundedFiniteSlot?
    (pointwiseSelectedSourceLocalLayerSerialFaceInputPortAt_card_le_four
      formation corridor hinterior offset)

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot?_slot
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (port : PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt formation
      corridor hinterior offset) :
    pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot? formation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialFaceInputPortSlotAt formation
          corridor hinterior offset port) = some port := by
  apply boundedFiniteSlot?_slot

/-- One graph-free fixed type for the selected predecessor facial attachment
state. -/
abbrev PointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentState :=
  BoundedCappedSupportedPortResidualCode (Fin 24) (Fin 4)

/-- Pad the exact dependent selected state to twenty-four dart slots and four
fragment slots. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    PointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentState :=
  padCappedSupportedPortResidualCodePorts
    (pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot? formation
      corridor hinterior offset)
    (padCappedSupportedPortResidualCode
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot?
        formation corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt
        formation corridor hinterior offset))

/-- A represented dart is present exactly when its literal edge belongs to the
selected terminal-aware predecessor region. -/
theorem pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
      formation corridor hinterior offset hcell).interfacePresent
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart) =
      decide (formation.annular.RS.edgeOf dart.1 ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset) := by
  simp [pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt,
    pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt]

/-- The selected component cap is exactly the cap at five of the distinct
primal edges in the full predecessor face component. -/
theorem pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_componentCap
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
      formation corridor hinterior offset hcell).componentCap
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart) =
      ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges
          formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            formation corridor hinterior offset) dart.1).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
  simp [pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt,
    pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt]

/-- The fixed selected state recovers complete predecessor facial
reachability on every represented transition-carrier dart. -/
theorem pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (left right : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    SupportedPortResidualFactoredReachability
        (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
          formation corridor hinterior offset hcell
          ).toBoundedSupportedPortResidualCode
        (fun leftPort rightPort : Fin 4 => leftPort = rightPort)
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell left)
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell right) ↔
      (faceRegionalDartGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset)).Reachable left.1 right.1 := by
  let region :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset
  let graph := faceRegionalDartGraph formation.annular.RS region
  let cut := indexedCrossingEdgeSet
    (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
      hinterior offset)
  let dartAt := fun dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset} => dart.1
  let portAt := fun port :
      PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt formation corridor
        hinterior offset =>
    (boundaryRegionalFragmentDartOccurrence formation.annular.RS cut region
      port).1
  let dependent :=
    pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt formation
      corridor hinterior offset
  have hexact : graph.Reachable (dartAt left) (dartAt right) ↔
      SupportedPortResidualFactoredReachability
        dependent.toBoundedSupportedPortResidualCode
        (fun leftPort rightPort :
          PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt formation
            corridor hinterior offset => leftPort = rightPort)
        left right := by
    apply reachable_iff_exactSupportedPortResidualFactoredReachability
    · intro leftPort rightPort hports
      subst rightPort
      exact SimpleGraph.Reachable.rfl
    · intro leftPort rightPort _hleft _hright hreachable
      exact (boundaryRegionalFragmentDartOccurrence_reachable_iff_eq
        formation.annular.RS cut region leftPort rightPort).1 hreachable
  unfold pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
  unfold pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot?
  rw [supportedPortResidualFactoredReachability_padPorts_boundedFiniteSlot
    (pointwiseSelectedSourceLocalLayerSerialFaceInputPortAt_card_le_four
      formation corridor hinterior offset)]
  change SupportedPortResidualFactoredReachability
      (padCappedSupportedPortResidualCode
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot?
          formation corridor hinterior offset hcell)
        dependent).toBoundedSupportedPortResidualCode
      (fun leftPort rightPort :
        PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt formation
          corridor hinterior offset => leftPort = rightPort)
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
        corridor hinterior offset hcell left)
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
        corridor hinterior offset hcell right) ↔ _
  simp only [SupportedPortResidualFactoredReachability,
    PortResidualFactoredReachability, padCappedSupportedPortResidualCode,
    padSupportedPortResidualCode,
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot?_slot]
  exact hexact.symm

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
