import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellSplicedTrackedFiniteClosure

/-!
# A finite support letter for a compatible prefix/Cell splice

The cumulative prefix and a literal Cell may be realized by different color
functions.  Under their explicit compatibility on the actual overlap, this
file packages the spliced pre-rebase output as the same finite support letter
used by the ambient specialization.

Only the color-sensitive tracked code changes.  The occurrence-sensitive
facial carrier, predecessor state, output-fragment representatives, port
representatives, and capped-length decoder are geometric and are reused
unchanged.  This proves all five pre-rebase profile coordinates for an
arbitrary compatible Cell witness; it does not yet construct compatibility
from the source boundary packet or apply the following boundary rebase.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellSplicedFiniteSupportLetter

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOldEdgeAdequacy
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellSplicedTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The finite support letter realized by an arbitrary compatible literal
Cell coloring.  Its input and facial attachment data come from the actual
cumulative prefix; its output and tracked local code use the spliced color. -/
noncomputable def sourceLocalLayerSerialSplicedCellFiniteSupportLetterAt
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
    (offset : Fin (blockLength - 3))
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    SourceLocalLayerSerialCellFiniteSupportLetter := by
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique offset
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let output := sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt
    corridor hunique offset coloring cellColor hcellColor
  exact {
    input := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
      offset
    output := output
    outputColor := output.profile.edgeColor
    trackedState := sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData
      caps coloring web corridor hunique offset
    trackedCode := sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData
      minimal caps coloring web corridor hunique offset splice
    trackedOutputSlot := fun step =>
      sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
        coloring web corridor hunique offset
        (sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData caps
          coloring web corridor hunique offset step)
    faceState := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    faceCode := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
      hcell
    faceEdgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
      offset hcell
    faceOutputSlot := fun fragment =>
      sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset hcell
        (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
          offset
          (boundaryRegionalFragmentAt web.annular.RS
            (indexedCrossingEdgeSet
              (sourceLocalLayerRightCrossingAt corridor hunique offset))
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset) fragment))
    facePortSlot := fun port side =>
      sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset hcell
        (sourceLocalLayerSerialFaceOutputPortTransitionDartAt corridor hunique
          offset port side)
    faceRole := sourceLocalLayerSerialOutputFaceRoleCodeAt corridor hunique offset
  }

/-- Every compatible prefix/Cell splice is supported by the same exact finite
letter relation as the ambient specialization. -/
theorem sourceLocalLayerSerialSplicedCellFiniteSupportLetterAt_supports
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
    (offset : Fin (blockLength - 3))
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    SourceLocalLayerSerialCellFiniteSupports
      (sourceLocalLayerSerialSplicedCellFiniteSupportLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellColor) := by
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique offset
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  have hsplice : ∀ step,
      splice (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := by
    intro step
    dsimp only [splice]
    rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
      offset coloring cellColor step]
    exact hcellColor step
  let input := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
    hunique offset
  let output := sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt
    corridor hunique offset coloring cellColor hcellColor
  let trackedState := sourceLocalLayerSerialTrackedPrefixAttachmentStateAt
    graphData caps coloring web corridor hunique offset
  let trackedCode := sourceLocalLayerSerialTrackedTransitionCodeForColorAt
    graphData minimal caps coloring web corridor hunique offset splice
  let faceState := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let faceCode := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
    offset hcell
  let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
    offset hcell
  unfold SourceLocalLayerSerialCellFiniteSupports
  dsimp only [sourceLocalLayerSerialSplicedCellFiniteSupportLetterAt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro step
    rfl
  · intro pair left right
    rw [sourceLocalLayerSerialSplicedPreRebaseOutput_strandConnected_iff_finiteClosure
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcompatible hcellColor pair left right]
    constructor
    · rintro ⟨hleftColor, hrightColor, hclosure⟩
      refine ⟨hleftColor, hrightColor, ?_⟩
      refine ⟨
        carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset)
          (sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData caps
            coloring web corridor hunique offset left),
        carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset)
          (sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData caps
            coloring web corridor hunique offset right), ?_, ?_, hclosure⟩
      · rfl
      · rfl
    · rintro ⟨hleftColor, hrightColor, leftCoordinate, rightCoordinate,
        hleftSlot, hrightSlot, hclosure⟩
      refine ⟨hleftColor, hrightColor, ?_⟩
      have hleft : leftCoordinate =
          carrierCoordinate
            (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset)
            (sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData caps
              coloring web corridor hunique offset left) := by
        apply Fin.ext
        simpa [BoundedCarrierLiveSlot,
          sourceLocalLayerSerialTrackedTransitionSlotAt] using
          congrArg Fin.val hleftSlot
      have hright : rightCoordinate =
          carrierCoordinate
            (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset)
            (sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData caps
              coloring web corridor hunique offset right) := by
        apply Fin.ext
        simpa [BoundedCarrierLiveSlot,
          sourceLocalLayerSerialTrackedTransitionSlotAt] using
          congrArg Fin.val hrightSlot
      simpa [hleft, hright] using hclosure
  · intro left right
    simpa [sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt,
      sourceLocalLayerSerialPreRebaseOutputBoundedProfileForColorAt,
      sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt,
      regionalBoundaryBoundedProfile,
      GraphCorridorCutData.regionalProfile] using
      (sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt_faceContinues_iff_roleCode
        corridor hunique offset left right)
  · intro fragment port
    dsimp only [sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt,
      sourceLocalLayerSerialPreRebaseOutputBoundedProfileForColorAt,
      regionalBoundaryBoundedProfile]
    let actualFragment := boundaryRegionalFragmentAt web.annular.RS
      (indexedCrossingEdgeSet
        (sourceLocalLayerRightCrossingAt corridor hunique offset))
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      fragment
    constructor
    · intro hprofile
      have hfinite :=
        (sourceLocalLayerSerialFaceOutputFragmentContainsPortFinite_iff_profile
          corridor hunique offset hcell splice hsplice fragment port).2 hprofile
      rcases hfinite with ⟨side, hclosure⟩
      refine ⟨side, ?_⟩
      refine ⟨
        carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset)
          (sourceLocalLayerSerialFaceOutputPortTransitionDartAt corridor hunique
            offset port side),
        carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset)
          (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
            hunique offset actualFragment), ?_, ?_, hclosure⟩
      · rfl
      · rfl
    · rintro ⟨side, leftCoordinate, rightCoordinate, hleftSlot, hrightSlot,
        hclosure⟩
      have hleft : leftCoordinate =
          carrierCoordinate
            (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset)
            (sourceLocalLayerSerialFaceOutputPortTransitionDartAt corridor
              hunique offset port side) := by
        apply Fin.ext
        simpa [BoundedCarrierLiveSlot,
          sourceLocalLayerSerialFaceTransitionSlotAt,
          GoertzelV24FramedTrail.boundedFiniteSlot, carrierCoordinate] using
          congrArg Fin.val hleftSlot
      have hright : rightCoordinate =
          carrierCoordinate
            (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset)
            (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
              hunique offset actualFragment) := by
        apply Fin.ext
        simpa [BoundedCarrierLiveSlot,
          sourceLocalLayerSerialFaceTransitionSlotAt,
          GoertzelV24FramedTrail.boundedFiniteSlot, carrierCoordinate,
          actualFragment] using
          congrArg Fin.val hrightSlot
      have hsource :
          SourceLocalLayerSerialFaceOutputFragmentContainsPortFinite corridor
            hunique offset hcell actualFragment port := by
        refine ⟨side, ?_⟩
        simpa [hleft, hright] using hclosure
      exact
        (sourceLocalLayerSerialFaceOutputFragmentContainsPortFinite_iff_profile
          corridor hunique offset hcell splice hsplice fragment port).1 hsource
  · intro fragment
    let actualFragment := boundaryRegionalFragmentAt web.annular.RS
      (indexedCrossingEdgeSet
        (sourceLocalLayerRightCrossingAt corridor hunique offset))
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      fragment
    let actualOutput := carrierCoordinate
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset)
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset actualFragment)
    let predecessorSemantic :=
      sourceLocalLayerSerialFaceFinitePredecessorSemanticAt corridor hunique
        offset hcell
    let newEdgeSemantic := sourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt
      corridor hunique offset hcell actualOutput
    refine ⟨actualOutput, rfl, predecessorSemantic, newEdgeSemantic, ?_⟩
    change SourceLocalLayerSerialFaceFiniteOutputCap faceState faceCode
        predecessorSemantic edgeState actualOutput newEdgeSemantic =
      output.profile.faceLengthCap fragment
    have hnamed :
        SourceLocalLayerSerialFaceFiniteOutputCap faceState faceCode
            predecessorSemantic edgeState actualOutput newEdgeSemantic =
          sourceLocalLayerSerialFaceFiniteOutputCapAt corridor hunique offset
            hcell actualFragment := by
      rfl
    rw [hnamed]
    have hcap := sourceLocalLayerSerialFaceFiniteOutputCapAt_eq_fragmentCap
      corridor hunique offset hcell actualFragment
    rw [hcap]
    apply Fin.ext
    change min
        (boundaryRegionalFragmentEdges web.annular.RS
          (indexedCrossingEdgeSet
            (sourceLocalLayerRightCrossingAt corridor hunique offset))
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          actualFragment).card 5 =
      (output.profile.faceLengthCap fragment).val
    rw [show boundaryRegionalFragmentEdges web.annular.RS
        (indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset))
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        actualFragment =
      (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
        ).regionalFragmentEdges fragment by
      rw [(sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique
        offset).regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
          (sourceLocalLayerSerialPreRebaseOutputCutDataAt_fragmentsOnFaceInRegion
            corridor hunique offset)]
      rfl]
    exact (GraphCorridorCutData.regionalProfile_faceLengthCap_val
      (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset)
      splice hsplice fragment).symm

end

end GoertzelV24ClosedWebLocalLayerSerialCellSplicedFiniteSupportLetter

end Mettapedia.GraphTheory.FourColor
