import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedFiniteClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteAmbientContinuation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputPort

/-!
# A complete finite support letter for a pointwise-selected Cell

This file joins the selected tracked and facial decoders into the fixed finite
letter consumed by the rooted Cell machine.  Its predecessor may be an
arbitrary cumulative prefix.  A positive literal Cell supplies its own colour
function, and the only compatibility condition is agreement on the actual
terminal-aware overlap.

Every one of the five outgoing profile fields is recovered exactly from the
finite receipt.  The construction uses interior-face uniqueness only at the
selected literal crossings and never the refuted global shared-edge receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedCellFiniteSupportLetter

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOldEdgeAdequacy
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteEdgeState
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputPort
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOldEdgeAdequacy
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteRepresentatives
open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedCellFiniteSupportLetterEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- At live tracked coordinates, the existential stable-slot wrapper is
exactly the underlying finite closure. -/
theorem sourceLocalLayerSerialTrackedFiniteConnected_liveSlot_iff
    (state :
      GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState.SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (code : BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerSerialTrackedFiniteConnected state input code pair
        (BoundedCarrierLiveSlot code left) (BoundedCarrierLiveSlot code right) ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialTrackedFiniteComponentStep state input code pair)
        left right := by
  constructor
  · rintro ⟨leftCoordinate, rightCoordinate, hleft, hright, hclosure⟩
    have hleftCoordinate : leftCoordinate = left := by
      apply Fin.ext
      have hvalue := congrArg (fun slot : Fin 21 => slot.val) hleft
      simpa [BoundedCarrierLiveSlot] using hvalue
    have hrightCoordinate : rightCoordinate = right := by
      apply Fin.ext
      have hvalue := congrArg (fun slot : Fin 21 => slot.val) hright
      simpa [BoundedCarrierLiveSlot] using hvalue
    simpa [hleftCoordinate, hrightCoordinate] using hclosure
  · intro hclosure
    exact ⟨left, right, rfl, rfl, hclosure⟩

/-- The analogous elimination rule for live facial coordinates. -/
theorem sourceLocalLayerSerialFaceFiniteConnected_liveSlot_iff
    (state :
      GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation.SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerSerialFaceFiniteConnected state code
        (BoundedCarrierLiveSlot code left) (BoundedCarrierLiveSlot code right) ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialFaceFiniteComponentStep state code) left right := by
  constructor
  · rintro ⟨leftCoordinate, rightCoordinate, hleft, hright, hclosure⟩
    have hleftCoordinate : leftCoordinate = left := by
      apply Fin.ext
      have hvalue := congrArg (fun slot : Fin 24 => slot.val) hleft
      simpa [BoundedCarrierLiveSlot] using hvalue
    have hrightCoordinate : rightCoordinate = right := by
      apply Fin.ext
      have hvalue := congrArg (fun slot : Fin 24 => slot.val) hright
      simpa [BoundedCarrierLiveSlot] using hvalue
    simpa [hleftCoordinate, hrightCoordinate] using hclosure
  · intro hclosure
    exact ⟨left, right, rfl, rfl, hclosure⟩

/-- Specialize live-slot elimination to the selected facial closure.  The
selected and generic steps share the same fixed ABI definitionally. -/
theorem sourceLocalLayerSerialFaceFiniteConnected_liveSlot_iff_pointwiseSelected
    (state : PointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerSerialFaceFiniteConnected state code
        (BoundedCarrierLiveSlot code left) (BoundedCarrierLiveSlot code right) ↔
      Relation.ReflTransGen
        (PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep state code)
        left right := by
  rw [sourceLocalLayerSerialFaceFiniteConnected_liveSlot_iff]
  rfl

/-- Extract the complete finite receipt of an arbitrary compatible prefix and
one positive pointwise-selected literal Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    SourceLocalLayerSerialCellFiniteSupportLetter := by
  let cellColor := pointwiseSelectedSourceLocalLayerCellLiteralColorAt
    web.toFormation corridor hinterior offset cellColoring
  let output :=
    pointwiseSelectedSourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt
      web.toFormation corridor hinterior offset prefixColor cellColoring
  exact {
    input :=
      pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
        web.toFormation corridor hinterior offset prefixColor hprefix
    output := output
    outputColor := output.profile.edgeColor
    trackedState :=
      pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
        web corridor hinterior offset prefixColor
    trackedCode := pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors
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
    trackedOutputSlot := fun step =>
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
        corridor hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialTrackedOutgoingPointAt
          web.toFormation corridor hinterior offset step)
    faceState :=
      pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
        web.toFormation corridor hinterior offset hcell
    faceCode := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt
      web.toFormation corridor hinterior offset hcell
    faceEdgeState :=
      pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt
        web.toFormation corridor hinterior offset hcell
    faceOutputSlot := fun fragment =>
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt web.toFormation
        corridor hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
          web.toFormation corridor hinterior offset
          (boundaryRegionalFragmentAt web.annular.RS
            (indexedCrossingEdgeSet
              (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
                corridor hinterior offset))
            (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
              web.toFormation corridor hinterior offset) fragment))
    facePortSlot := fun port side =>
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt web.toFormation
        corridor hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputPortTransitionDartAt
          web.toFormation corridor hinterior offset port side)
    faceRole :=
      pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleCodeAt web.toFormation
        corridor hinterior offset
  }

/-- Every compatible arbitrary prefix and positive literal selected Cell
satisfies the complete five-coordinate finite support relation. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt_supports
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        web.toFormation corridor hinterior offset prefixColor
        (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
          corridor hinterior offset cellColoring)) :
    SourceLocalLayerSerialCellFiniteSupports
      (pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt web
        corridor hinterior offset hcell prefixColor hprefix cellColoring) := by
  let cellColor := pointwiseSelectedSourceLocalLayerCellLiteralColorAt
    web.toFormation corridor hinterior offset cellColoring
  let spliced := pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
    web.toFormation corridor hinterior offset prefixColor cellColor
  let input :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
      web.toFormation corridor hinterior offset prefixColor hprefix
  let output :=
    pointwiseSelectedSourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt
      web.toFormation corridor hinterior offset prefixColor cellColoring
  let trackedState :=
    pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
      web corridor hinterior offset prefixColor
  let trackedCode :=
    pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors
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
  let faceState :=
    pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
      web.toFormation corridor hinterior offset hcell
  let faceCode := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt
    web.toFormation corridor hinterior offset hcell
  let edgeState :=
    pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt web.toFormation
      corridor hinterior offset hcell
  unfold SourceLocalLayerSerialCellFiniteSupports
  dsimp only [pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro step
    rfl
  · intro pair left right
    let data :=
      pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt
        web.toFormation corridor hinterior offset
    have hspliced : ∀ step, spliced (data.crossingEdge step) ≠ 0 := by
      intro step
      change spliced
          (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
            corridor hinterior offset step) ≠ 0
      dsimp only [spliced]
      rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
        web.toFormation corridor hinterior offset]
      · exact
          pointwiseSelectedSourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero
            web.toFormation corridor hinterior offset cellColoring step
      · exact pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing
          web.toFormation corridor hinterior offset step
    let leftPoint :=
      pointwiseSelectedSourceLocalLayerSerialTrackedOutgoingPointAt
        web.toFormation corridor hinterior offset left
    let rightPoint :=
      pointwiseSelectedSourceLocalLayerSerialTrackedOutgoingPointAt
        web.toFormation corridor hinterior offset right
    have hfinite :=
      pointwiseSelectedSourceLocalLayerSerialPreRebaseTrackedReachableForCompatibleColors_iff_finiteClosure
        web corridor hinterior offset hcell prefixColor cellColor hprefix
          hcompatible pair leftPoint rightPoint
    have hleftProfileColor :
        (output.profile.edgeColor left).toColor =
          spliced (data.portEdge (.inl left)) := by
      change ((data.regionalProfile spliced hspliced).edgeColor left).toColor = _
      simpa [GraphCorridorCutData.portEdge] using
        data.regionalProfile_edgeColor_toColor spliced hspliced left
    have hrightProfileColor :
        (output.profile.edgeColor right).toColor =
          spliced (data.portEdge (.inl right)) := by
      change ((data.regionalProfile spliced hspliced).edgeColor right).toColor = _
      simpa [GraphCorridorCutData.portEdge] using
        data.regionalProfile_edgeColor_toColor spliced hspliced right
    change (data.regionalProfile spliced hspliced).strandConnected pair
        (.inl left) (.inl right) = true ↔ _
    rw [data.regionalProfile_strandConnected_eq_true_iff]
    constructor
    · rintro ⟨_hleftPort, _hrightPort, hleftColor, hrightColor, hreachable⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hleftProfileColor]
        exact hleftColor
      · rw [hrightProfileColor]
        exact hrightColor
      · change SourceLocalLayerSerialTrackedFiniteConnected trackedState input
          trackedCode pair
          (BoundedCarrierLiveSlot trackedCode
            (carrierCoordinate
              (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
                web.toFormation corridor hinterior offset) leftPoint))
          (BoundedCarrierLiveSlot trackedCode
            (carrierCoordinate
              (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
                web.toFormation corridor hinterior offset) rightPoint))
        rw [sourceLocalLayerSerialTrackedFiniteConnected_liveSlot_iff]
        exact hfinite.1 hreachable
    · rintro ⟨hleftColor, hrightColor, hconnected⟩
      refine ⟨
        pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt_portsInRegion
          web.toFormation corridor hinterior offset (.inl left),
        pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt_portsInRegion
          web.toFormation corridor hinterior offset (.inl right), ?_, ?_, ?_⟩
      · rw [← hleftProfileColor]
        exact hleftColor
      · rw [← hrightProfileColor]
        exact hrightColor
      · apply hfinite.2
        have hconnected' :
            SourceLocalLayerSerialTrackedFiniteConnected trackedState input
          trackedCode pair
          (BoundedCarrierLiveSlot trackedCode
            (carrierCoordinate
              (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
                web.toFormation corridor hinterior offset) leftPoint))
          (BoundedCarrierLiveSlot trackedCode
            (carrierCoordinate
              (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
                web.toFormation corridor hinterior offset) rightPoint)) :=
          hconnected
        exact
          (sourceLocalLayerSerialTrackedFiniteConnected_liveSlot_iff _ _ _ _ _
            _).1 hconnected'
  · intro left right
    exact
      pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputBoundedProfileAt_faceContinues_iff_roleCode
        web.toFormation corridor hinterior offset spliced
          (fun step => by
            dsimp only [spliced]
            rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
              web.toFormation corridor hinterior offset]
            · exact
                pointwiseSelectedSourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero
                  web.toFormation corridor hinterior offset cellColoring step
            · exact pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing
                web.toFormation corridor hinterior offset step)
          left right
  · intro fragment port
    let actualFragment := boundaryRegionalFragmentAt web.annular.RS
      (indexedCrossingEdgeSet
        (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
          corridor hinterior offset))
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
        web.toFormation corridor hinterior offset) fragment
    have hprofile :=
      pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentContainsPortFinite_iff_profile
        web.toFormation corridor hinterior offset hcell spliced
        (fun step => by
          dsimp only [spliced]
          rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
            web.toFormation corridor hinterior offset]
          · exact
              pointwiseSelectedSourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero
                web.toFormation corridor hinterior offset cellColoring step
          · exact pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing
              web.toFormation corridor hinterior offset step)
        fragment port
    constructor
    · intro hcontains
      rcases hprofile.2 hcontains with ⟨side, hclosure⟩
      refine ⟨side, ?_⟩
      change SourceLocalLayerSerialFaceFiniteConnected faceState faceCode
        (BoundedCarrierLiveSlot faceCode
          (carrierCoordinate
            (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
              web.toFormation corridor hinterior offset)
            (pointwiseSelectedSourceLocalLayerSerialFaceOutputPortTransitionDartAt
              web.toFormation corridor hinterior offset port side)))
        (BoundedCarrierLiveSlot faceCode
          (carrierCoordinate
            (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
              web.toFormation corridor hinterior offset)
            (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
              web.toFormation corridor hinterior offset actualFragment)))
      rw [sourceLocalLayerSerialFaceFiniteConnected_liveSlot_iff_pointwiseSelected]
      simpa [faceState, faceCode, actualFragment] using hclosure
    · rintro ⟨side, hconnected⟩
      apply hprofile.1
      refine ⟨side, ?_⟩
      have hconnected' :
          SourceLocalLayerSerialFaceFiniteConnected faceState faceCode
            (BoundedCarrierLiveSlot faceCode
              (carrierCoordinate
                (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
                  web.toFormation corridor hinterior offset)
                (pointwiseSelectedSourceLocalLayerSerialFaceOutputPortTransitionDartAt
                  web.toFormation corridor hinterior offset port side)))
            (BoundedCarrierLiveSlot faceCode
              (carrierCoordinate
                (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
                  web.toFormation corridor hinterior offset)
                (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
                  web.toFormation corridor hinterior offset actualFragment))) :=
        hconnected
      have hclosure :=
        (sourceLocalLayerSerialFaceFiniteConnected_liveSlot_iff_pointwiseSelected
          _ _ _ _).1 hconnected'
      simpa [faceState, faceCode, actualFragment] using hclosure
  · intro fragment
    let actualFragment := boundaryRegionalFragmentAt web.annular.RS
      (indexedCrossingEdgeSet
        (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
          corridor hinterior offset))
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
        web.toFormation corridor hinterior offset) fragment
    let actualOutput := carrierCoordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior offset)
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
        web.toFormation corridor hinterior offset actualFragment)
    let predecessorSemantic :=
      pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt
        web.toFormation corridor hinterior offset hcell
    let newEdgeSemantic :=
      pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt
        web.toFormation corridor hinterior offset hcell actualOutput
    refine ⟨actualOutput, rfl, predecessorSemantic, newEdgeSemantic, ?_⟩
    change SourceLocalLayerSerialFaceFiniteOutputCap faceState faceCode
        predecessorSemantic edgeState actualOutput newEdgeSemantic =
      output.profile.faceLengthCap fragment
    have hnamed :
        SourceLocalLayerSerialFaceFiniteOutputCap faceState faceCode
            predecessorSemantic edgeState actualOutput newEdgeSemantic =
          pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCapAt
            web.toFormation corridor hinterior offset hcell actualFragment := by
      rfl
    rw [hnamed]
    have hcap :=
      pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCapAt_eq_fragmentCap
        web.toFormation corridor hinterior offset hcell actualFragment
    rw [hcap]
    apply Fin.ext
    change min
        (boundaryRegionalFragmentEdges web.annular.RS
          (indexedCrossingEdgeSet
            (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
              corridor hinterior offset))
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
            web.toFormation corridor hinterior offset)
          actualFragment).card 5 =
      (output.profile.faceLengthCap fragment).val
    rw [show boundaryRegionalFragmentEdges web.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
            corridor hinterior offset))
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
          web.toFormation corridor hinterior offset)
        actualFragment =
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt
        web.toFormation corridor hinterior offset).regionalFragmentEdges
          fragment by
      rw [(pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt
        web.toFormation corridor hinterior offset
        ).regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt_fragmentsOnFaceInRegion
            web.toFormation corridor hinterior offset)]
      rfl]
    exact (GraphCorridorCutData.regionalProfile_faceLengthCap_val
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt
        web.toFormation corridor hinterior offset)
      spliced
      (fun step => by
        dsimp only [spliced]
        rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
          web.toFormation corridor hinterior offset]
        · exact
            pointwiseSelectedSourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero
              web.toFormation corridor hinterior offset cellColoring step
        · exact pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing
            web.toFormation corridor hinterior offset step)
      fragment).symm

end

end GoertzelV24ClosedWebPointwiseSelectedCellFiniteSupportLetter

end Mettapedia.GraphTheory.FourColor
