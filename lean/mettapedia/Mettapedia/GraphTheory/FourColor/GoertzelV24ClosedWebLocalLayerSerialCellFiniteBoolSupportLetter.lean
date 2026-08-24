import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteCapReflection

/-!
# An executable five-field support letter for one literal source Cell

The proof-facing finite support letter stores proposition-valued local graph
families.  This module mirrors it with native Boolean adjacency tables and
combines the already reflected colour, tracked-connectivity, facial,
port-incidence, and capped-progress conditions into one executable predicate.

The crown theorem proves that reflecting any proof-facing letter preserves its
support proposition exactly.  The letter remains indexed by the complete
literal Cell data; no quotient by the three geometric orientation labels is
introduced here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteCapReflection
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteStepReflection
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

/-- Native Boolean form of one complete heterogeneous literal Cell letter. -/
structure SourceLocalLayerSerialCellFiniteBoolSupportLetter where
  input : BoundedCorridorCutProfile 2 1 4
  output : BoundedCorridorCutProfile 2 0 4
  outputColor : Fin 2 → StrandColor
  trackedState : SourceLocalLayerSerialTrackedPrefixAttachmentState
  trackedCode : BoundedCarrierBoolGraphFamilyCode 21 5
    (TrackedColorPair × Bool)
  trackedOutputSlot : Fin 2 → Fin 21
  faceState : SourceLocalLayerSerialFacePrefixAttachmentState
  faceCode : BoundedCarrierBoolGraphFamilyCode 24 0 Bool
  faceEdgeState : SourceLocalLayerSerialFaceFiniteEdgeState
  faceOutputSlot : Fin output.faceFragmentCount.val → Fin 24
  facePortSlot : Fin 2 → Fin 2 → Fin 24
  faceRole : Fin output.faceFragmentCount.val →
    SourceLocalLayerSerialOutputFaceRole

noncomputable instance :
    DecidableEq SourceLocalLayerSerialCellFiniteBoolSupportLetter :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialCellFiniteBoolSupportLetterCode :=
  BoundedCorridorCutProfile 2 1 4 ×
    Σ output : BoundedCorridorCutProfile 2 0 4,
      ((Fin 2 → StrandColor) ×
        SourceLocalLayerSerialTrackedPrefixAttachmentState ×
        BoundedCarrierBoolGraphFamilyCode 21 5 (TrackedColorPair × Bool) ×
        (Fin 2 → Fin 21)) ×
      (SourceLocalLayerSerialFacePrefixAttachmentState ×
        BoundedCarrierBoolGraphFamilyCode 24 0 Bool ×
        SourceLocalLayerSerialFaceFiniteEdgeState ×
        (Fin 2 → Fin 2 → Fin 24)) ×
      (Fin output.faceFragmentCount.val → Fin 24) ×
      (Fin output.faceFragmentCount.val →
        SourceLocalLayerSerialOutputFaceRole)

private def sourceLocalLayerSerialCellFiniteBoolSupportLetterEquiv :
    SourceLocalLayerSerialCellFiniteBoolSupportLetter ≃
      sourceLocalLayerSerialCellFiniteBoolSupportLetterCode where
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
      faceRole := faceRole }
  left_inv letter := by cases letter; rfl
  right_inv data := by
    rcases data with ⟨input, ⟨output,
      ⟨outputColor, trackedState, trackedCode, trackedOutputSlot⟩,
      ⟨faceState, faceCode, faceEdgeState, facePortSlot⟩,
      faceOutputSlot, faceRole⟩⟩
    rfl

deriving noncomputable instance Fintype for
  sourceLocalLayerSerialCellFiniteBoolSupportLetterCode

noncomputable instance :
    Fintype SourceLocalLayerSerialCellFiniteBoolSupportLetter := by
  exact Fintype.ofEquiv _
    sourceLocalLayerSerialCellFiniteBoolSupportLetterEquiv.symm

/-- Reflect a proof-facing finite letter into native Boolean graph tables. -/
noncomputable def ofFiniteSupportLetter
    (letter : SourceLocalLayerSerialCellFiniteSupportLetter) :
    SourceLocalLayerSerialCellFiniteBoolSupportLetter where
  input := letter.input
  output := letter.output
  outputColor := letter.outputColor
  trackedState := letter.trackedState
  trackedCode := ofGraphFamilyCode letter.trackedCode
  trackedOutputSlot := letter.trackedOutputSlot
  faceState := letter.faceState
  faceCode := ofGraphFamilyCode letter.faceCode
  faceEdgeState := letter.faceEdgeState
  faceOutputSlot := letter.faceOutputSlot
  facePortSlot := letter.facePortSlot
  faceRole := letter.faceRole

/-- Executable support predicate for all five outgoing profile coordinates of
one native Boolean literal Cell letter. -/
def SourceLocalLayerSerialCellFiniteSupportsBool
    (letter : SourceLocalLayerSerialCellFiniteBoolSupportLetter) : Bool :=
  decide
    ((∀ step,
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
            SourceLocalLayerSerialTrackedFiniteConnectedBool
              letter.trackedState letter.input letter.trackedCode pair
              (letter.trackedOutputSlot left)
                (letter.trackedOutputSlot right) = true)) ∧
      (∀ left right,
        (letter.output.profile.faceContinues left right = true ↔
          letter.faceRole left = letter.faceRole right)) ∧
      (∀ fragment port,
        (letter.output.profile.fragmentContainsPort fragment (.inl port) =
            true ↔
          ∃ side : Fin 2,
            SourceLocalLayerSerialFaceFiniteConnectedBool letter.faceState
              letter.faceCode (letter.facePortSlot port side)
                (letter.faceOutputSlot fragment) = true)) ∧
      (∀ fragment,
        SourceLocalLayerSerialFaceFiniteCapAtBool letter.faceState
          letter.faceCode letter.faceEdgeState
          (letter.faceOutputSlot fragment)
            (letter.output.profile.faceLengthCap fragment) = true))

/-- Reflection of a proof-facing letter preserves the complete five-field
support relation exactly. -/
@[simp]
theorem finiteSupportsBool_ofFiniteSupportLetter_eq_true_iff
    (letter : SourceLocalLayerSerialCellFiniteSupportLetter) :
    SourceLocalLayerSerialCellFiniteSupportsBool
        (ofFiniteSupportLetter letter) = true ↔
      SourceLocalLayerSerialCellFiniteSupports letter := by
  rw [SourceLocalLayerSerialCellFiniteSupportsBool, decide_eq_true_eq]
  unfold SourceLocalLayerSerialCellFiniteSupports
  simp only [ofFiniteSupportLetter,
    trackedFiniteConnectedBool_ofGraphFamilyCode_eq_true_iff,
    faceFiniteConnectedBool_ofGraphFamilyCode_eq_true_iff,
    capAtBool_ofGraphFamilyCode_eq_true_iff]

end GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter

end Mettapedia.GraphTheory.FourColor
