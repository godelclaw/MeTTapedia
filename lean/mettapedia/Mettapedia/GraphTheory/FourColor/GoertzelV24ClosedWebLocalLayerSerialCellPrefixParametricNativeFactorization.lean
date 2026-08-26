import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellSplicedFiniteSupportLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor

/-!
# Prefix-parametric physical Cell factorization

One positive literal Cell is packaged as a prefix-independent finite factor.
For every arbitrary cumulative prefix colouring with nonzero displayed cut
edges, literal overlap compatibility is sufficient for the factor's executable
support guard.  The reconstructed five-field letter is exactly the source
splice, with no ambient-prefix specialization hidden in its tables.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeFactorization

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOldEdgeAdequacy
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeCode
open GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricTrackedClosure
open GoertzelV24ClosedWebLocalLayerSerialCellSplicedFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric
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

local instance prefixParametricNativeFactorizationOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The five-field proof-facing letter of an arbitrary compatible cumulative
prefix and literal Cell colouring. -/
noncomputable def sourceLocalLayerSerialSplicedCellFiniteSupportLetterForColorAt
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    SourceLocalLayerSerialCellFiniteSupportLetter := by
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique offset
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  let output := sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt
    corridor hunique offset prefixColor cellColor hcellColor
  exact {
    input := terminalInputBoundedProfileForColorAt corridor hunique offset
      prefixColor hprefixCrossing
    output := output
    outputColor := output.profile.edgeColor
    trackedState := sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
      graphData caps coloring web corridor hunique offset prefixColor
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

/-- Every literal compatible prefix/Cell splice satisfies all five coordinates
of its prefix-parametric finite support letter. -/
theorem sourceLocalLayerSerialSplicedCellFiniteSupportLetterForColorAt_supports
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    SourceLocalLayerSerialCellFiniteSupports
      (sourceLocalLayerSerialSplicedCellFiniteSupportLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellColor) := by
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique offset
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  have hsplice : ∀ step,
      splice (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := by
    intro step
    dsimp only [splice]
    rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
      offset prefixColor cellColor step]
    exact hcellColor step
  let input := terminalInputBoundedProfileForColorAt corridor hunique offset
    prefixColor hprefixCrossing
  let output := sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt
    corridor hunique offset prefixColor cellColor hcellColor
  let trackedState := sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
    graphData caps coloring web corridor hunique offset prefixColor
  let trackedCode := sourceLocalLayerSerialTrackedTransitionCodeForColorAt
    graphData minimal caps coloring web corridor hunique offset splice
  let faceState := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let faceCode := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
    offset hcell
  let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
    offset hcell
  unfold SourceLocalLayerSerialCellFiniteSupports
  dsimp only [sourceLocalLayerSerialSplicedCellFiniteSupportLetterForColorAt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro step
    rfl
  · intro pair left right
    rw [sourceLocalLayerSerialSplicedPreRebaseOutputForColor_strandConnected_iff_finiteClosure
      graphData minimal caps coloring web corridor hunique offset prefixColor
        cellColor hprefixCrossing hcompatible hcellColor pair left right]
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

/-- Exact prefix-parametric state/output/local-factor package for a literal
Cell.  Only the cumulative state contains prefix-specific data. -/
noncomputable def sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    SourceLocalLayerSerialCellPhysicalBoolFactoredLetter := by
  let letter := sourceLocalLayerSerialSplicedCellFiniteSupportLetterForColorAt
    graphData minimal caps coloring web corridor hunique offset prefixColor
      hprefixCrossing cellColor hcellColor
  exact ⟨
    sourceLocalLayerSerialColoredCumulativeStateForColorAt graphData minimal caps
      coloring web corridor hunique offset prefixColor hprefixCrossing,
    letter.output, {
      outputColor := letter.outputColor
      trackedGeometry := ofGraphFamilyCode
        (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
          coloring web corridor hunique offset)
      trackedCellColor := sourceLocalLayerSerialCarrierColorCodeAt graphData caps
        coloring web corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor
      trackedOutputSlot := letter.trackedOutputSlot
      faceCode := ofGraphFamilyCode letter.faceCode
      faceEdgeState := letter.faceEdgeState
      faceOutputSlot := letter.faceOutputSlot
      facePortSlot := letter.facePortSlot
      faceRole := letter.faceRole
    }⟩

/-- Native reconstruction of the prefix-parametric package is definitionally
the Boolean reflection of its exact five-field proof-facing letter. -/
theorem
    sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt_reassembles
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    let factored :=
      sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellColor
    reassemblePhysicalBoolSupportLetter factored.1 factored.2.1 factored.2.2 =
      ofFiniteSupportLetter
        (sourceLocalLayerSerialSplicedCellFiniteSupportLetterForColorAt graphData
          minimal caps coloring web corridor hunique offset prefixColor
            hprefixCrossing cellColor hcellColor) := by
  dsimp only [sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt,
    sourceLocalLayerSerialColoredCumulativeStateForColorAt,
    reassemblePhysicalBoolSupportLetter]
  rw [sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_eq_reflection,
    sourceLocalLayerSerialTrackedCodeOfFiniteColorsForColorAt_eq]
  dsimp only [ofFiniteSupportLetter,
    sourceLocalLayerSerialSplicedCellFiniteSupportLetterForColorAt]

/-- Every compatible arbitrary prefix/literal-Cell pair passes the executable
physical transition guard. -/
theorem sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt_supports
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    let factored :=
      sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellColor
    SourceLocalLayerSerialCellPhysicalSupportsBool factored.1 factored.2.1
      factored.2.2 = true := by
  dsimp only [SourceLocalLayerSerialCellPhysicalSupportsBool]
  rw [Bool.and_eq_true]
  constructor
  · rw [sourceLocalLayerSerialCarrierColorsCompatibleBool_eq_true_iff]
    simpa only [sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt,
      sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
      (sourceLocalLayerSerialCarrierColorsCompatibleForColor_iff graphData
        minimal caps coloring web corridor hunique offset prefixColor
          cellColor).2 hcompatible
  · rw [
      sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt_reassembles,
      finiteSupportsBool_ofFiniteSupportLetter_eq_true_iff]
    exact
      sourceLocalLayerSerialSplicedCellFiniteSupportLetterForColorAt_supports
        graphData minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcompatible hcellColor

end

end GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeFactorization

end Mettapedia.GraphTheory.FourColor
