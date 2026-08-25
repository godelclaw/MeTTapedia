import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceTransitionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFaceFixedState

/-!
# Finite predecessor facial attachments on the source-Cell carrier

The Cell and residual seam share a carrier of at most twenty-four literal
darts.  A predecessor face component may leave this local carrier and return,
so its contribution cannot be replaced by an induced local graph.

This file extracts the exact predecessor component state relative to the
actual terminal-aware input fragments, pads occurrences to `Fin 24` and
fragments to `Fin 4`, and retains regional presence plus the cap at five of
the distinct primal edges in each component.  The adequacy theorem recovers
complete predecessor facial reachability on every represented dart.

This is source-image predecessor state.  It stores no successor relation and
does not yet perform the Cell/seam closure or decode the outgoing profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

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
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFacePrefixAttachmentStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The actual occurrence-sensitive input boundary fragments used as
persistent ports of the predecessor facial state. -/
abbrev SourceLocalLayerSerialFaceInputPortAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :=
  BoundaryRegionalFragment web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerLeftCrossingAt corridor hunique offset))
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)

/-- A two-edge cut has at most four occurrence-sensitive predecessor
fragments, including on the opened one-sided carrier. -/
theorem sourceLocalLayerSerialFaceInputPortAt_card_le_four
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    Fintype.card (SourceLocalLayerSerialFaceInputPortAt corridor hunique offset)
      ≤ 4 := by
  exact regionalBoundaryGraphCutData_fragmentCount_le_two_mul
    web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    (sourceLocalLayerLeftCrossingAt corridor hunique offset)

/-- Exact capped predecessor data on the dependent literal carrier and actual
input-fragment ports. -/
abbrev SourceLocalLayerSerialFacePrefixAttachmentCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :=
  BoundedCappedSupportedPortResidualCode
    {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}
    (SourceLocalLayerSerialFaceInputPortAt corridor hunique offset)

/-- Extract exact predecessor component attachments, literal regional
presence, and distinct-edge caps from the terminal-aware input region. -/
noncomputable def sourceLocalLayerSerialFacePrefixAttachmentCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialFacePrefixAttachmentCodeAt corridor hunique offset := by
  classical
  let region := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    offset
  let graph := faceRegionalDartGraph web.annular.RS region
  let cut := indexedCrossingEdgeSet
    (sourceLocalLayerLeftCrossingAt corridor hunique offset)
  let dartAt := fun dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset} =>
    dart.1
  let portAt := fun port : SourceLocalLayerSerialFaceInputPortAt corridor
      hunique offset =>
    (boundaryRegionalFragmentDartOccurrence web.annular.RS cut region port).1
  exact {
    toBoundedSupportedPortResidualCode :=
      exactSupportedPortResidualCode graph dartAt portAt
    interfacePresent := fun dart =>
      decide (web.annular.RS.edgeOf dart.1 ∈ region)
    componentCap := fun dart =>
      ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          region dart.1).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ }

/-- Canonical fixed slot of a dart in the common transition carrier. -/
noncomputable def sourceLocalLayerSerialFaceTransitionSlotAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset} →
      Fin 24 :=
  boundedFiniteSlot
    (by
      simpa [Fintype.card_subtype] using
        sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
          corridor hunique offset hcell)

/-- Partial inverse of the fixed transition slot map. -/
noncomputable def sourceLocalLayerSerialFaceTransitionDartAtSlot?
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    Fin 24 → Option {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset} :=
  boundedFiniteSlot?
    (by
      simpa [Fintype.card_subtype] using
        sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
          corridor hunique offset hcell)

@[simp]
theorem sourceLocalLayerSerialFaceTransitionDartAtSlot?_slot
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset hcell
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell dart) = some dart := by
  apply boundedFiniteSlot?_slot

/-- A live fixed facial slot is uniquely the canonical slot of the dart it
decodes.  This is the right-inverse form needed when a later occurrence
receipt searches the padded predecessor carrier. -/
theorem sourceLocalLayerSerialFaceTransitionDartAtSlot?_eq_some_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : Fin 24)
    (dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
        hcell slot = some dart ↔
      slot = sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
        hcell dart := by
  apply boundedFiniteSlot?_eq_some_iff

/-- Fixed slot and partial decoder for actual predecessor fragments. -/
noncomputable def sourceLocalLayerSerialFaceInputPortSlotAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialFaceInputPortAt corridor hunique offset → Fin 4 :=
  boundedFiniteSlot
    (sourceLocalLayerSerialFaceInputPortAt_card_le_four corridor hunique offset)

noncomputable def sourceLocalLayerSerialFaceInputPortAtSlot?
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    Fin 4 → Option
      (SourceLocalLayerSerialFaceInputPortAt corridor hunique offset) :=
  boundedFiniteSlot?
    (sourceLocalLayerSerialFaceInputPortAt_card_le_four corridor hunique offset)

@[simp]
theorem sourceLocalLayerSerialFaceInputPortAtSlot?_slot
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (port : SourceLocalLayerSerialFaceInputPortAt corridor hunique offset) :
    sourceLocalLayerSerialFaceInputPortAtSlot? corridor hunique offset
        (sourceLocalLayerSerialFaceInputPortSlotAt corridor hunique offset port) =
      some port := by
  apply boundedFiniteSlot?_slot

/-- One graph-free fixed type for the predecessor facial attachment state. -/
abbrev SourceLocalLayerSerialFacePrefixAttachmentState :=
  BoundedCappedSupportedPortResidualCode (Fin 24) (Fin 4)

/-- Pad the exact dependent source state to twenty-four dart slots and four
fragment slots. -/
noncomputable def sourceLocalLayerSerialFacePrefixAttachmentStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    SourceLocalLayerSerialFacePrefixAttachmentState :=
  padCappedSupportedPortResidualCodePorts
    (sourceLocalLayerSerialFaceInputPortAtSlot? corridor hunique offset)
    (padCappedSupportedPortResidualCode
      (sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
        hcell)
      (sourceLocalLayerSerialFacePrefixAttachmentCodeAt corridor hunique offset))

/-- A represented dart is marked present exactly when its literal edge lies
in the terminal-aware predecessor region. -/
theorem sourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique offset
      hcell).interfacePresent
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell dart) =
      decide (web.annular.RS.edgeOf dart.1 ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) := by
  simp [sourceLocalLayerSerialFacePrefixAttachmentStateAt,
    sourceLocalLayerSerialFacePrefixAttachmentCodeAt]

/-- The cap stored at a represented dart is exactly the cap at five of the
distinct primal edges in its full predecessor face component. -/
theorem sourceLocalLayerSerialFacePrefixAttachmentStateAt_componentCap
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique offset
      hcell).componentCap
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell dart) =
      ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          dart.1).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
  simp [sourceLocalLayerSerialFacePrefixAttachmentStateAt,
    sourceLocalLayerSerialFacePrefixAttachmentCodeAt]

/-- The padded predecessor state recovers complete predecessor facial
reachability on every represented transition-carrier dart. -/
theorem sourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    SupportedPortResidualFactoredReachability
        (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique
          offset hcell).toBoundedSupportedPortResidualCode
        (fun leftPort rightPort : Fin 4 => leftPort = rightPort)
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell left)
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell right) ↔
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        ).Reachable left.1 right.1 := by
  let region := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    offset
  let graph := faceRegionalDartGraph web.annular.RS region
  let cut := indexedCrossingEdgeSet
    (sourceLocalLayerLeftCrossingAt corridor hunique offset)
  let dartAt := fun dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset} =>
    dart.1
  let portAt := fun port : SourceLocalLayerSerialFaceInputPortAt corridor
      hunique offset =>
    (boundaryRegionalFragmentDartOccurrence web.annular.RS cut region port).1
  let dependent := sourceLocalLayerSerialFacePrefixAttachmentCodeAt corridor
    hunique offset
  have hexact : graph.Reachable (dartAt left) (dartAt right) ↔
      SupportedPortResidualFactoredReachability
        dependent.toBoundedSupportedPortResidualCode
        (fun leftPort rightPort : SourceLocalLayerSerialFaceInputPortAt corridor
          hunique offset => leftPort = rightPort) left right := by
    apply reachable_iff_exactSupportedPortResidualFactoredReachability
    · intro leftPort rightPort hports
      subst rightPort
      exact SimpleGraph.Reachable.rfl
    · intro leftPort rightPort _hleft _hright hreachable
      exact (boundaryRegionalFragmentDartOccurrence_reachable_iff_eq
        web.annular.RS cut region leftPort rightPort).1 hreachable
  unfold sourceLocalLayerSerialFacePrefixAttachmentStateAt
  unfold sourceLocalLayerSerialFaceInputPortAtSlot?
  rw [supportedPortResidualFactoredReachability_padPorts_boundedFiniteSlot
    (sourceLocalLayerSerialFaceInputPortAt_card_le_four corridor hunique offset)]
  change SupportedPortResidualFactoredReachability
      (padCappedSupportedPortResidualCode
        (sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
          hcell) dependent).toBoundedSupportedPortResidualCode
      (fun leftPort rightPort : SourceLocalLayerSerialFaceInputPortAt corridor
        hunique offset => leftPort = rightPort)
      (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
        hcell left)
      (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
        hcell right) ↔ _
  simp only [SupportedPortResidualFactoredReachability,
    PortResidualFactoredReachability, padCappedSupportedPortResidualCode,
    padSupportedPortResidualCode,
    sourceLocalLayerSerialFaceTransitionDartAtSlot?_slot]
  exact hexact.symm

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
