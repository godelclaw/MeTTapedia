import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter

/-!
# Separate cumulative state from one literal Cell factor

The finite support letter was initially packaged as one record containing both
the accumulated prefix state and the bounded local Cell data.  That record is
finite, but it is not yet a pumpable alphabet: deleting or repeating a Cell
must not duplicate the state accumulated before that Cell.

This file gives the exact representation factorization used by the executable
transfer construction.  A transition is split into:

* the complete cumulative input state;
* one bounded local Cell factor, independent of that cumulative state;
* the candidate output profile.

Splitting and reassembly are inverse equivalences, and the old support
predicate is definitionally the new three-argument transition relation.  Thus
this step loses no information and introduces no over-approximation.  It is a
representation theorem only: completeness with respect to every positive
entry of the manuscript's literal `Count` matrix is the next obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellStateFactorization

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

/-- All data inherited from the corridor prefix before the next literal Cell.
Unlike the former support-letter record, this state contains no successor
profile and no local Cell graph. -/
structure SourceLocalLayerSerialCumulativeState where
  input : BoundedCorridorCutProfile 2 1 4
  tracked : SourceLocalLayerSerialTrackedPrefixAttachmentState
  face : SourceLocalLayerSerialFacePrefixAttachmentState

noncomputable instance :
    DecidableEq SourceLocalLayerSerialCumulativeState :=
  Classical.decEq _

deriving noncomputable instance Fintype for
  SourceLocalLayerSerialCumulativeState

/-- The proof-facing bounded local factor for one Cell and its outgoing seam.
The dependent fragment coordinates are indexed by the candidate output count,
but no cumulative prefix state occurs here. -/
structure SourceLocalLayerSerialCellFiniteLocalFactor
    (outputCount : Fin 5) where
  outputColor : Fin 2 → StrandColor
  trackedCode : BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool)
  trackedOutputSlot : Fin 2 → Fin 21
  faceCode : BoundedCarrierGraphFamilyCode 24 0 Bool
  faceEdgeState : SourceLocalLayerSerialFaceFiniteEdgeState
  faceOutputSlot : Fin outputCount.val → Fin 24
  facePortSlot : Fin 2 → Fin 2 → Fin 24
  faceRole : Fin outputCount.val → SourceLocalLayerSerialOutputFaceRole

noncomputable instance (outputCount : Fin 5) :
    DecidableEq (SourceLocalLayerSerialCellFiniteLocalFactor outputCount) :=
  Classical.decEq _

/-- Native Boolean form of the same prefix-independent bounded local factor. -/
structure SourceLocalLayerSerialCellFiniteBoolLocalFactor
    (outputCount : Fin 5) where
  outputColor : Fin 2 → StrandColor
  trackedCode : BoundedCarrierBoolGraphFamilyCode 21 5
    (TrackedColorPair × Bool)
  trackedOutputSlot : Fin 2 → Fin 21
  faceCode : BoundedCarrierBoolGraphFamilyCode 24 0 Bool
  faceEdgeState : SourceLocalLayerSerialFaceFiniteEdgeState
  faceOutputSlot : Fin outputCount.val → Fin 24
  facePortSlot : Fin 2 → Fin 2 → Fin 24
  faceRole : Fin outputCount.val → SourceLocalLayerSerialOutputFaceRole

noncomputable instance (outputCount : Fin 5) :
    DecidableEq (SourceLocalLayerSerialCellFiniteBoolLocalFactor outputCount) :=
  Classical.decEq _

/-- Exact factored representation of a proof-facing finite support letter. -/
abbrev SourceLocalLayerSerialCellFiniteFactoredLetter :=
  SourceLocalLayerSerialCumulativeState ×
    Σ output : BoundedCorridorCutProfile 2 0 4,
      SourceLocalLayerSerialCellFiniteLocalFactor output.faceFragmentCount

/-- Exact factored representation of a native Boolean support letter. -/
abbrev SourceLocalLayerSerialCellFiniteBoolFactoredLetter :=
  SourceLocalLayerSerialCumulativeState ×
    Σ output : BoundedCorridorCutProfile 2 0 4,
      SourceLocalLayerSerialCellFiniteBoolLocalFactor output.faceFragmentCount

/-- Split the proof-facing record into state, output and local factor. -/
def splitFiniteSupportLetter
    (letter : SourceLocalLayerSerialCellFiniteSupportLetter) :
    SourceLocalLayerSerialCellFiniteFactoredLetter :=
  ⟨{
      input := letter.input
      tracked := letter.trackedState
      face := letter.faceState
    },
    letter.output,
    {
      outputColor := letter.outputColor
      trackedCode := letter.trackedCode
      trackedOutputSlot := letter.trackedOutputSlot
      faceCode := letter.faceCode
      faceEdgeState := letter.faceEdgeState
      faceOutputSlot := letter.faceOutputSlot
      facePortSlot := letter.facePortSlot
      faceRole := letter.faceRole
    }⟩

/-- Reassemble a proof-facing support letter from its three exact factors. -/
def reassembleFiniteSupportLetter
    (factored : SourceLocalLayerSerialCellFiniteFactoredLetter) :
    SourceLocalLayerSerialCellFiniteSupportLetter := by
  rcases factored with ⟨state, output, localFactor⟩
  exact {
    input := state.input
    output := output
    outputColor := localFactor.outputColor
    trackedState := state.tracked
    trackedCode := localFactor.trackedCode
    trackedOutputSlot := localFactor.trackedOutputSlot
    faceState := state.face
    faceCode := localFactor.faceCode
    faceEdgeState := localFactor.faceEdgeState
    faceOutputSlot := localFactor.faceOutputSlot
    facePortSlot := localFactor.facePortSlot
    faceRole := localFactor.faceRole
  }

@[simp]
theorem reassembleFiniteSupportLetter_split
    (letter : SourceLocalLayerSerialCellFiniteSupportLetter) :
    reassembleFiniteSupportLetter (splitFiniteSupportLetter letter) = letter := by
  cases letter
  rfl

@[simp]
theorem splitFiniteSupportLetter_reassemble
    (factored : SourceLocalLayerSerialCellFiniteFactoredLetter) :
    splitFiniteSupportLetter (reassembleFiniteSupportLetter factored) =
      factored := by
  rcases factored with ⟨state, output, localFactor⟩
  cases state
  cases localFactor
  rfl

/-- The old proof-facing letter type is exactly a state/output/local-factor
sigma type. -/
def finiteSupportLetterEquivFactored :
    SourceLocalLayerSerialCellFiniteSupportLetter ≃
      SourceLocalLayerSerialCellFiniteFactoredLetter where
  toFun := splitFiniteSupportLetter
  invFun := reassembleFiniteSupportLetter
  left_inv := reassembleFiniteSupportLetter_split
  right_inv := splitFiniteSupportLetter_reassemble

noncomputable instance :
    Fintype SourceLocalLayerSerialCellFiniteFactoredLetter := by
  exact Fintype.ofEquiv SourceLocalLayerSerialCellFiniteSupportLetter
    finiteSupportLetterEquivFactored

/-- Split the native Boolean record into state, output and local factor. -/
def splitFiniteBoolSupportLetter
    (letter : SourceLocalLayerSerialCellFiniteBoolSupportLetter) :
    SourceLocalLayerSerialCellFiniteBoolFactoredLetter :=
  ⟨{
      input := letter.input
      tracked := letter.trackedState
      face := letter.faceState
    },
    letter.output,
    {
      outputColor := letter.outputColor
      trackedCode := letter.trackedCode
      trackedOutputSlot := letter.trackedOutputSlot
      faceCode := letter.faceCode
      faceEdgeState := letter.faceEdgeState
      faceOutputSlot := letter.faceOutputSlot
      facePortSlot := letter.facePortSlot
      faceRole := letter.faceRole
    }⟩

/-- Reassemble a native Boolean support letter from its exact factors. -/
def reassembleFiniteBoolSupportLetter
    (factored : SourceLocalLayerSerialCellFiniteBoolFactoredLetter) :
    SourceLocalLayerSerialCellFiniteBoolSupportLetter := by
  rcases factored with ⟨state, output, localFactor⟩
  exact {
    input := state.input
    output := output
    outputColor := localFactor.outputColor
    trackedState := state.tracked
    trackedCode := localFactor.trackedCode
    trackedOutputSlot := localFactor.trackedOutputSlot
    faceState := state.face
    faceCode := localFactor.faceCode
    faceEdgeState := localFactor.faceEdgeState
    faceOutputSlot := localFactor.faceOutputSlot
    facePortSlot := localFactor.facePortSlot
    faceRole := localFactor.faceRole
  }

@[simp]
theorem reassembleFiniteBoolSupportLetter_split
    (letter : SourceLocalLayerSerialCellFiniteBoolSupportLetter) :
    reassembleFiniteBoolSupportLetter (splitFiniteBoolSupportLetter letter) =
      letter := by
  cases letter
  rfl

@[simp]
theorem splitFiniteBoolSupportLetter_reassemble
    (factored : SourceLocalLayerSerialCellFiniteBoolFactoredLetter) :
    splitFiniteBoolSupportLetter (reassembleFiniteBoolSupportLetter factored) =
      factored := by
  rcases factored with ⟨state, output, localFactor⟩
  cases state
  cases localFactor
  rfl

/-- The executable letter type has the same exact state/output/local-factor
decomposition. -/
def finiteBoolSupportLetterEquivFactored :
    SourceLocalLayerSerialCellFiniteBoolSupportLetter ≃
      SourceLocalLayerSerialCellFiniteBoolFactoredLetter where
  toFun := splitFiniteBoolSupportLetter
  invFun := reassembleFiniteBoolSupportLetter
  left_inv := reassembleFiniteBoolSupportLetter_split
  right_inv := splitFiniteBoolSupportLetter_reassemble

noncomputable instance :
    Fintype SourceLocalLayerSerialCellFiniteBoolFactoredLetter := by
  exact Fintype.ofEquiv SourceLocalLayerSerialCellFiniteBoolSupportLetter
    finiteBoolSupportLetterEquivFactored

/-- The factored proof-facing transition relation. -/
def SourceLocalLayerSerialCellFiniteFactoredSupports
    (state : SourceLocalLayerSerialCumulativeState)
    (output : BoundedCorridorCutProfile 2 0 4)
    (localFactor : SourceLocalLayerSerialCellFiniteLocalFactor
      output.faceFragmentCount) : Prop :=
  SourceLocalLayerSerialCellFiniteSupports
    (reassembleFiniteSupportLetter ⟨state, output, localFactor⟩)

/-- The native executable factored transition predicate. -/
def SourceLocalLayerSerialCellFiniteFactoredSupportsBool
    (state : SourceLocalLayerSerialCumulativeState)
    (output : BoundedCorridorCutProfile 2 0 4)
    (localFactor : SourceLocalLayerSerialCellFiniteBoolLocalFactor
      output.faceFragmentCount) : Bool :=
  SourceLocalLayerSerialCellFiniteSupportsBool
    (reassembleFiniteBoolSupportLetter ⟨state, output, localFactor⟩)

/-- Exact support factorization for every proof-facing record. -/
@[simp]
theorem finiteFactoredSupports_split_iff
    (letter : SourceLocalLayerSerialCellFiniteSupportLetter) :
    (let factored := splitFiniteSupportLetter letter;
      SourceLocalLayerSerialCellFiniteFactoredSupports factored.1
        factored.2.1 factored.2.2) ↔
      SourceLocalLayerSerialCellFiniteSupports letter := by
  simp [SourceLocalLayerSerialCellFiniteFactoredSupports]

/-- Exact executable support factorization for every native record. -/
@[simp]
theorem finiteBoolFactoredSupports_split
    (letter : SourceLocalLayerSerialCellFiniteBoolSupportLetter) :
    (let factored := splitFiniteBoolSupportLetter letter;
      SourceLocalLayerSerialCellFiniteFactoredSupportsBool factored.1
        factored.2.1 factored.2.2) =
      SourceLocalLayerSerialCellFiniteSupportsBool letter := by
  simp [SourceLocalLayerSerialCellFiniteFactoredSupportsBool]

/-- Reflection preserves the cumulative state exactly. -/
@[simp]
theorem splitFiniteBoolSupportLetter_ofFiniteSupportLetter_state
    (letter : SourceLocalLayerSerialCellFiniteSupportLetter) :
    (splitFiniteBoolSupportLetter (ofFiniteSupportLetter letter)).1 =
      (splitFiniteSupportLetter letter).1 := by
  rfl

/-- Reflection preserves the candidate output exactly. -/
@[simp]
theorem splitFiniteBoolSupportLetter_ofFiniteSupportLetter_output
    (letter : SourceLocalLayerSerialCellFiniteSupportLetter) :
    (splitFiniteBoolSupportLetter (ofFiniteSupportLetter letter)).2.1 =
      (splitFiniteSupportLetter letter).2.1 := by
  rfl

/-- Reflection preserves the factored support relation exactly. -/
@[simp]
theorem finiteBoolFactoredSupports_ofFiniteSupportLetter_eq_true_iff
    (letter : SourceLocalLayerSerialCellFiniteSupportLetter) :
    (let factored :=
        splitFiniteBoolSupportLetter (ofFiniteSupportLetter letter);
      SourceLocalLayerSerialCellFiniteFactoredSupportsBool factored.1
          factored.2.1 factored.2.2 = true) ↔
      SourceLocalLayerSerialCellFiniteSupports letter := by
  change SourceLocalLayerSerialCellFiniteSupportsBool
      (reassembleFiniteBoolSupportLetter
        (splitFiniteBoolSupportLetter (ofFiniteSupportLetter letter))) = true ↔
    SourceLocalLayerSerialCellFiniteSupports letter
  rw [reassembleFiniteBoolSupportLetter_split]
  exact finiteSupportsBool_ofFiniteSupportLetter_eq_true_iff letter

end GoertzelV24ClosedWebLocalLayerSerialCellStateFactorization

end Mettapedia.GraphTheory.FourColor
