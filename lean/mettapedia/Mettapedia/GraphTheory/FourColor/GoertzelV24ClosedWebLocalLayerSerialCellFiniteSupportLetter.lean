import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure

/-!
# A finite support letter for one literal source Cell

The source corridor is a heterogeneous word of literal Cells.  This file
packages one letter without replacing it by one of the three geometric slab
orientations.  Its data are the complete incoming and outgoing five-field
profiles together with fixed finite codes for the tracked and facial local
factors.

The relation below is deliberately one-sided: every actual source Cell
produces a supported finite letter.  The converse identification with the
positive support of the manuscript's `Count` matrix, and the reachable closure
of the resulting heterogeneous word, are later obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOldEdgeAdequacy
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

/-- A live coordinate of a bounded carrier, embedded in its stable slots. -/
def BoundedCarrierLiveSlot
    {bound portCount : Nat} {index : Type*}
    (code : BoundedCarrierGraphFamilyCode bound portCount index)
    (coordinate : Fin code.vertexCount.val) : Fin bound :=
  Fin.castLE (Nat.le_of_lt_succ code.vertexCount.isLt) coordinate

/-- A graph-free tracked closure on the stable twenty-one-slot ABI. -/
def SourceLocalLayerSerialTrackedFiniteConnected
    (state : SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (code : BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool))
    (pair : TrackedColorPair) (left right : Fin 21) : Prop :=
  ∃ leftCoordinate rightCoordinate : Fin code.vertexCount.val,
    BoundedCarrierLiveSlot code leftCoordinate = left ∧
    BoundedCarrierLiveSlot code rightCoordinate = right ∧
    Relation.ReflTransGen
      (SourceLocalLayerSerialTrackedFiniteComponentStep state input code pair)
      leftCoordinate rightCoordinate

/-- A graph-free facial closure on the stable twenty-four-slot ABI. -/
def SourceLocalLayerSerialFaceFiniteConnected
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin 24) : Prop :=
  ∃ leftCoordinate rightCoordinate : Fin code.vertexCount.val,
    BoundedCarrierLiveSlot code leftCoordinate = left ∧
    BoundedCarrierLiveSlot code rightCoordinate = right ∧
    Relation.ReflTransGen
      (SourceLocalLayerSerialFaceFiniteComponentStep state code)
      leftCoordinate rightCoordinate

/-- The fixed finite data of one heterogeneous literal Cell letter.  The
output-fragment slots are dependent only on the already finite output count. -/
structure SourceLocalLayerSerialCellFiniteSupportLetter where
  input : BoundedCorridorCutProfile 2 1 4
  output : BoundedCorridorCutProfile 2 0 4
  outputColor : Fin 2 → StrandColor
  trackedState : SourceLocalLayerSerialTrackedPrefixAttachmentState
  trackedCode : BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool)
  trackedOutputSlot : Fin 2 → Fin 21
  faceState : SourceLocalLayerSerialFacePrefixAttachmentState
  faceCode : BoundedCarrierGraphFamilyCode 24 0 Bool
  faceEdgeState : SourceLocalLayerSerialFaceFiniteEdgeState
  faceOutputSlot : Fin output.faceFragmentCount.val → Fin 24
  facePortSlot : Fin 2 → Fin 2 → Fin 24
  faceRole : Fin output.faceFragmentCount.val →
    SourceLocalLayerSerialOutputFaceRole

noncomputable instance :
    DecidableEq SourceLocalLayerSerialCellFiniteSupportLetter :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialCellFiniteSupportLetterCode :=
  BoundedCorridorCutProfile 2 1 4 ×
    Σ output : BoundedCorridorCutProfile 2 0 4,
      ((Fin 2 → StrandColor) ×
        SourceLocalLayerSerialTrackedPrefixAttachmentState ×
        BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool) ×
        (Fin 2 → Fin 21)) ×
      (SourceLocalLayerSerialFacePrefixAttachmentState ×
        BoundedCarrierGraphFamilyCode 24 0 Bool ×
        SourceLocalLayerSerialFaceFiniteEdgeState ×
        (Fin 2 → Fin 2 → Fin 24)) ×
      (Fin output.faceFragmentCount.val → Fin 24) ×
      (Fin output.faceFragmentCount.val →
        SourceLocalLayerSerialOutputFaceRole)

private def sourceLocalLayerSerialCellFiniteSupportLetterEquiv :
    SourceLocalLayerSerialCellFiniteSupportLetter ≃
      sourceLocalLayerSerialCellFiniteSupportLetterCode where
  toFun letter :=
    ⟨letter.input, ⟨letter.output,
      ⟨letter.outputColor, letter.trackedState, letter.trackedCode,
        letter.trackedOutputSlot⟩,
      ⟨letter.faceState, letter.faceCode, letter.faceEdgeState,
        letter.facePortSlot⟩,
      letter.faceOutputSlot, letter.faceRole⟩⟩
  invFun data := by
    rcases data with ⟨input, ⟨output,
      ⟨outputColor, trackedState, trackedCode, trackedOutputSlot⟩,
      ⟨faceState, faceCode, faceEdgeState, facePortSlot⟩,
      faceOutputSlot, faceRole⟩⟩
    exact {
      input := input
      output := output
      outputColor := outputColor
      trackedState := trackedState
      trackedCode := trackedCode
      trackedOutputSlot := trackedOutputSlot
      faceState := faceState
      faceCode := faceCode
      faceEdgeState := faceEdgeState
      faceOutputSlot := faceOutputSlot
      facePortSlot := facePortSlot
      faceRole := faceRole
    }
  left_inv letter := by cases letter; rfl
  right_inv data := by
    rcases data with ⟨input, ⟨output,
      ⟨outputColor, trackedState, trackedCode, trackedOutputSlot⟩,
      ⟨faceState, faceCode, faceEdgeState, facePortSlot⟩,
      faceOutputSlot, faceRole⟩⟩
    rfl

deriving noncomputable instance Fintype for
  sourceLocalLayerSerialCellFiniteSupportLetterCode

noncomputable instance :
    Fintype SourceLocalLayerSerialCellFiniteSupportLetter := by
  exact Fintype.ofEquiv _
    sourceLocalLayerSerialCellFiniteSupportLetterEquiv.symm

/-- The finite predecessor/new-edge cap computation, exposed as a relation so
that its semantic laws remain explicit rather than hidden in a choice. -/
def SourceLocalLayerSerialFaceFiniteCapAt
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (slot : Fin 24) (cap : Fin 6) : Prop :=
  ∃ output : Fin code.vertexCount.val,
    BoundedCarrierLiveSlot code output = slot ∧
    ∃ predecessorSemantic :
        SourceLocalLayerSerialFaceFinitePredecessorSemantic state code,
      ∃ newEdgeSemantic :
          SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code edgeState
            output,
        SourceLocalLayerSerialFaceFiniteOutputCap state code
          predecessorSemantic edgeState output newEdgeSemantic = cap

/-- All five outgoing profile coordinates are decoded by the finite letter.
This is a support relation, not yet the converse `Count > 0` theorem. -/
def SourceLocalLayerSerialCellFiniteSupports
    (letter : SourceLocalLayerSerialCellFiniteSupportLetter) : Prop :=
  (∀ step,
      letter.output.profile.edgeColor step = letter.outputColor step) ∧
  (∀ pair left right,
      (letter.output.profile.strandConnected pair (.inl left) (.inl right) =
          true ↔
        IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (letter.output.profile.edgeColor left).toColor ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (letter.output.profile.edgeColor right).toColor ∧
          SourceLocalLayerSerialTrackedFiniteConnected letter.trackedState
            letter.input letter.trackedCode pair
            (letter.trackedOutputSlot left) (letter.trackedOutputSlot right))) ∧
  (∀ left right,
      (letter.output.profile.faceContinues left right = true ↔
        letter.faceRole left = letter.faceRole right)) ∧
  (∀ fragment port,
      (letter.output.profile.fragmentContainsPort fragment (.inl port) = true ↔
        ∃ side : Fin 2,
          SourceLocalLayerSerialFaceFiniteConnected letter.faceState
            letter.faceCode (letter.facePortSlot port side)
              (letter.faceOutputSlot fragment))) ∧
  (∀ fragment,
      SourceLocalLayerSerialFaceFiniteCapAt letter.faceState letter.faceCode
        letter.faceEdgeState (letter.faceOutputSlot fragment)
          (letter.output.profile.faceLengthCap fragment))

noncomputable instance (letter : SourceLocalLayerSerialCellFiniteSupportLetter) :
    Decidable (SourceLocalLayerSerialCellFiniteSupports letter) :=
  Classical.propDecidable _

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

/-- Extract the finite support letter of one actual literal source Cell. -/
noncomputable def sourceLocalLayerSerialCellFiniteSupportLetterAt
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
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialCellFiniteSupportLetter := by
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique offset
  let output := sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor
    hunique offset
  exact {
    input := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
      offset
    output := output
    outputColor := output.profile.edgeColor
    trackedState := sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData
      caps coloring web corridor hunique offset
    trackedCode := sourceLocalLayerSerialTrackedTransitionCodeAt graphData minimal
      caps coloring web corridor hunique offset
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

/-- Every actual literal source Cell is included in the finite support
relation.  This is the sound direction needed before computing a conservative
reachable closure; it does not assert that every finite code is realizable. -/
theorem sourceLocalLayerSerialCellFiniteSupportLetterAt_supports
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
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialCellFiniteSupports
      (sourceLocalLayerSerialCellFiniteSupportLetterAt graphData minimal caps
        coloring web corridor hunique offset) := by
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique offset
  let input := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
    hunique offset
  let output := sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor
    hunique offset
  let trackedState := sourceLocalLayerSerialTrackedPrefixAttachmentStateAt
    graphData caps coloring web corridor hunique offset
  let trackedCode := sourceLocalLayerSerialTrackedTransitionCodeAt graphData
    minimal caps coloring web corridor hunique offset
  let faceState := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let faceCode := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
    offset hcell
  let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
    offset hcell
  let relation := sourceLocalLayerSerialCellFullProfileRelation_of_ambientColoring
    corridor hunique offset
  unfold SourceLocalLayerSerialCellFiniteSupports
  dsimp only [sourceLocalLayerSerialCellFiniteSupportLetterAt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro step
    rfl
  · intro pair left right
    rw [sourceLocalLayerSerialPreRebaseOutput_strandConnected_iff_finiteClosure
      graphData minimal caps coloring web corridor hunique offset pair left right]
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
    exact sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt_faceContinues_iff_roleCode
      corridor hunique offset left right
  · intro fragment port
    dsimp only [sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt,
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
          corridor hunique offset hcell coloring (fun _ => web.tait _)
          fragment port).2 hprofile
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
          corridor hunique offset hcell coloring (fun _ => web.tait _)
          fragment port).1 hsource
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
    have hprofile := relation.outputFaceLengthCap fragment
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
    exact hprofile.symm

end

end GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter

end Mettapedia.GraphTheory.FourColor
