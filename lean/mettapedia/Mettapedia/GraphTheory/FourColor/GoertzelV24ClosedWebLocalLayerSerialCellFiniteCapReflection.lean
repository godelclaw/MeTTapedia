import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteCapSemanticReflection

/-!
# Executable face-cap reflection for one literal Cell

The proof-facing face-cap decoder chooses quotient representatives using
semantic proof objects.  This module computes the same quantity directly on
the fixed live carrier.  A coordinate is canonical precisely when no smaller
coordinate belongs to its predecessor component or denotes the same genuinely
new primal edge.  The resulting finite sums are capped at five exactly as in
the source profile.

The reflection theorem is conditional only on the two Boolean law checks from
the preceding module, and identifies the executable cap query with the
existing proposition-valued support relation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFiniteCapReflection

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOldEdgeAdequacy
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteCapSemanticReflection
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteStepReflection
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter

/-- A live coordinate is the least name of its predecessor component. -/
def SourceLocalLayerSerialFaceFinitePredecessorRepresentativeBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (coordinate : Fin code.vertexCount.val) : Bool :=
  state.interfacePresent (BoundedCarrierBoolLiveSlot code coordinate) &&
    decide (∀ candidate,
      SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state code
          candidate coordinate = true →
        coordinate ≤ candidate)

/-- The least-coordinate test selects exactly the proof-facing canonical
predecessor representatives when the finite predecessor laws hold. -/
@[simp]
theorem predecessorRepresentativeBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (coordinate : Fin code.vertexCount.val) :
    SourceLocalLayerSerialFaceFinitePredecessorRepresentativeBool state
        (ofGraphFamilyCode code) coordinate = true ↔
      coordinate ∈
        sourceLocalLayerSerialFaceFinitePredecessorRepresentatives state code
          semantic := by
  simp only [SourceLocalLayerSerialFaceFinitePredecessorRepresentativeBool,
    Bool.and_eq_true, decide_eq_true_eq,
    mem_sourceLocalLayerSerialFaceFinitePredecessorRepresentatives_iff,
    BoundedCarrierBoolLiveSlot, sourceLocalLayerSerialFaceFiniteStableSlot]
  constructor
  · rintro ⟨hpresent, hleast⟩
    refine ⟨hpresent, le_antisymm ?_ ?_⟩
    · apply Finset.min'_le
      exact (mem_sourceLocalLayerSerialFaceFinitePredecessorPartition_part_iff
        state code semantic coordinate coordinate).2
          (semantic.connected_refl coordinate)
    · apply hleast
      exact (predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
        _ coordinate).2
          (semantic.connected_symm
            ((mem_sourceLocalLayerSerialFaceFinitePredecessorPartition_part_iff
              state code semantic coordinate _).1
              (sourceLocalLayerSerialFaceFinitePredecessorRepresentative_mem_part
                state code semantic coordinate)))
  · rintro ⟨hpresent, hrepresentative⟩
    refine ⟨hpresent, ?_⟩
    intro candidate hconnected
    change Fin code.vertexCount.val at candidate
    have hconnected' :=
      (predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
        candidate coordinate).1 hconnected
    have hrepresentatives :=
      (sourceLocalLayerSerialFaceFinitePredecessorRepresentative_eq_iff state
        code semantic candidate coordinate).2 hconnected'
    have hminimum :
        sourceLocalLayerSerialFaceFinitePredecessorRepresentative state code
            semantic candidate ≤ candidate :=
      Finset.min'_le _ candidate
        ((mem_sourceLocalLayerSerialFaceFinitePredecessorPartition_part_iff
          state code semantic candidate candidate).2
          (semantic.connected_refl candidate))
    rw [← hrepresentative]
    exact hrepresentatives.trans_le hminimum

/-- Canonical old components which reach one selected output coordinate. -/
def sourceLocalLayerSerialFaceFiniteContributingPredecessorsBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (output : Fin code.vertexCount.val) : Finset (Fin code.vertexCount.val) :=
  Finset.univ.filter fun representative =>
    SourceLocalLayerSerialFaceFinitePredecessorRepresentativeBool state code
        representative &&
      SourceLocalLayerSerialFaceFiniteComponentClosureBool state code output
        representative

/-- Boolean predecessor selection agrees exactly with the proof-facing
selection when its semantic laws hold. -/
theorem contributingPredecessorsBool_ofGraphFamilyCode_eq
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (output : Fin code.vertexCount.val) :
    sourceLocalLayerSerialFaceFiniteContributingPredecessorsBool state
        (ofGraphFamilyCode code) output =
      sourceLocalLayerSerialFaceFiniteContributingPredecessors state code
        semantic output := by
  classical
  unfold sourceLocalLayerSerialFaceFiniteContributingPredecessorsBool
  unfold sourceLocalLayerSerialFaceFiniteContributingPredecessors
  apply Finset.ext
  intro representative
  change Fin code.vertexCount.val at representative
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true]
  rw [predecessorRepresentativeBool_ofGraphFamilyCode_eq_true_iff state code
    semantic]
  rw [faceFiniteComponentClosureBool_ofGraphFamilyCode_eq_true_iff]
  exact ⟨Finset.mem_filter.mpr, Finset.mem_filter.mp⟩

/-- Executable capped contribution of all distinct predecessor components. -/
def sourceLocalLayerSerialFaceFinitePredecessorCapSumBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (output : Fin code.vertexCount.val) : Nat :=
  min
    (∑ representative ∈
      sourceLocalLayerSerialFaceFiniteContributingPredecessorsBool state code
        output,
      (state.componentCap
        (BoundedCarrierBoolLiveSlot code representative)).val)
    5

/-- The executable predecessor cap sum is the mathematical one. -/
theorem predecessorCapSumBool_ofGraphFamilyCode_eq
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (output : Fin code.vertexCount.val) :
    sourceLocalLayerSerialFaceFinitePredecessorCapSumBool state
        (ofGraphFamilyCode code) output =
      sourceLocalLayerSerialFaceFinitePredecessorCapSum state code semantic
        output := by
  unfold sourceLocalLayerSerialFaceFinitePredecessorCapSumBool
  unfold sourceLocalLayerSerialFaceFinitePredecessorCapSum
  rw [contributingPredecessorsBool_ofGraphFamilyCode_eq state code semantic
    output]
  rfl

/-- A genuinely new contributing coordinate is the least live name of its
underlying primal edge. -/
def SourceLocalLayerSerialFaceFiniteNewEdgeRepresentativeBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output coordinate : Fin code.vertexCount.val) : Bool :=
  SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool state code edgeState
      output coordinate &&
    decide (∀ candidate,
      SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool state code
          edgeState output candidate = true →
      edgeState.samePrimalEdge
          (BoundedCarrierBoolLiveSlot code candidate)
          (BoundedCarrierBoolLiveSlot code coordinate) = true →
        coordinate ≤ candidate)

/-- The least-coordinate test selects exactly one name for each genuinely new
primal edge when the equality-table laws hold. -/
@[simp]
theorem newEdgeRepresentativeBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val)
    (semantic : SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code
      edgeState output)
    (coordinate : Fin code.vertexCount.val) :
    SourceLocalLayerSerialFaceFiniteNewEdgeRepresentativeBool state
        (ofGraphFamilyCode code) edgeState output coordinate = true ↔
      coordinate ∈ sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state
        code edgeState output semantic := by
  simp only [SourceLocalLayerSerialFaceFiniteNewEdgeRepresentativeBool,
    Bool.and_eq_true, decide_eq_true_eq,
    mem_sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_iff,
    BoundedCarrierBoolLiveSlot]
  constructor
  · rintro ⟨hcontributes, hleast⟩
    let hcoordinate :=
      (newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code edgeState
        output coordinate).1 hcontributes
    refine ⟨hcoordinate, le_antisymm ?_ ?_⟩
    · apply Finset.min'_le
      exact (mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff state code
        edgeState output coordinate coordinate).2
          ⟨hcoordinate, semantic.same_refl coordinate hcoordinate⟩
    · apply hleast
      · exact (newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
          edgeState output _).2
          ((mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff state code
            edgeState output coordinate _).1
            (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_mem_class
              state code edgeState output semantic coordinate hcoordinate)).1
      · exact ((mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff state code
          edgeState output coordinate _).1
          (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_mem_class state
            code edgeState output semantic coordinate hcoordinate)).2
  · rintro ⟨hcoordinate, hrepresentative⟩
    refine ⟨(newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
      edgeState output coordinate).2 hcoordinate, ?_⟩
    intro candidate hcandidate hsame
    change Fin code.vertexCount.val at candidate
    let hcandidate' :=
      (newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code edgeState
        output candidate).1 hcandidate
    have hreps :=
      (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_eq_iff state code
        edgeState output semantic candidate coordinate hcandidate' hcoordinate
        ).2 hsame
    have hminimum :
        sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative state code
            edgeState output semantic candidate hcandidate' ≤ candidate :=
      Finset.min'_le _ candidate
        ((mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff state code
          edgeState output candidate candidate).2
          ⟨hcandidate', semantic.same_refl candidate hcandidate'⟩)
    rw [← hrepresentative]
    exact hreps.trans_le hminimum

/-- Canonical representatives of genuinely new edges in one output component. -/
def sourceLocalLayerSerialFaceFiniteNewEdgeRepresentativesBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val) : Finset (Fin code.vertexCount.val) :=
  Finset.univ.filter fun coordinate =>
    SourceLocalLayerSerialFaceFiniteNewEdgeRepresentativeBool state code
      edgeState output coordinate

/-- Boolean new-edge selection agrees with the proof-facing selection. -/
theorem newEdgeRepresentativesBool_ofGraphFamilyCode_eq
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val)
    (semantic : SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code
      edgeState output) :
    sourceLocalLayerSerialFaceFiniteNewEdgeRepresentativesBool state
        (ofGraphFamilyCode code) edgeState output =
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state code
        edgeState output semantic := by
  ext coordinate
  change Fin code.vertexCount.val at coordinate
  simp only [sourceLocalLayerSerialFaceFiniteNewEdgeRepresentativesBool,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [newEdgeRepresentativeBool_ofGraphFamilyCode_eq_true_iff state code
    edgeState output semantic]
  exact Iff.rfl

/-- Fully executable cap-at-five decoder for one live output coordinate. -/
def SourceLocalLayerSerialFaceFiniteOutputCapBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val) : Fin 6 :=
  ⟨min
      (sourceLocalLayerSerialFaceFinitePredecessorCapSumBool state code output +
        (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentativesBool state code
          edgeState output).card)
      5,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- The executable decoder computes exactly the proof-facing cap whenever both
finite semantic checks succeed. -/
theorem outputCapBool_ofGraphFamilyCode_eq
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (predecessorSemantic :
      SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (output : Fin code.vertexCount.val)
    (newEdgeSemantic : SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code
      edgeState output) :
    SourceLocalLayerSerialFaceFiniteOutputCapBool state (ofGraphFamilyCode code)
        edgeState output =
      SourceLocalLayerSerialFaceFiniteOutputCap state code predecessorSemantic
        edgeState output newEdgeSemantic := by
  apply Fin.ext
  simp only [SourceLocalLayerSerialFaceFiniteOutputCapBool,
    SourceLocalLayerSerialFaceFiniteOutputCap]
  rw [predecessorCapSumBool_ofGraphFamilyCode_eq state code
    predecessorSemantic output]
  rw [newEdgeRepresentativesBool_ofGraphFamilyCode_eq state code edgeState output
    newEdgeSemantic]
  rfl

/-- Executable cap support at one stable output slot.  Both semantic-law checks
are part of the accepted Boolean letter rather than hidden proof arguments. -/
def SourceLocalLayerSerialFaceFiniteCapAtBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (slot : Fin 24) (cap : Fin 6) : Bool :=
  SourceLocalLayerSerialFaceFinitePredecessorSemanticBool state code &&
    decide (∃ output : Fin code.vertexCount.val,
      BoundedCarrierBoolLiveSlot code output = slot ∧
        SourceLocalLayerSerialFaceFiniteNewEdgeSemanticBool state code edgeState
          output = true ∧
        SourceLocalLayerSerialFaceFiniteOutputCapBool state code edgeState
          output = cap)

/-- The executable cap query is exactly the original cap support relation on a
reflected proof-facing graph code. -/
@[simp]
theorem capAtBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (slot : Fin 24) (cap : Fin 6) :
    SourceLocalLayerSerialFaceFiniteCapAtBool state (ofGraphFamilyCode code)
        edgeState slot cap = true ↔
      SourceLocalLayerSerialFaceFiniteCapAt state code edgeState slot cap := by
  simp only [SourceLocalLayerSerialFaceFiniteCapAtBool, Bool.and_eq_true,
    predecessorSemanticBool_ofGraphFamilyCode_eq_true_iff,
    decide_eq_true_eq,
    newEdgeSemanticBool_ofGraphFamilyCode_eq_true_iff,
    SourceLocalLayerSerialFaceFiniteCapAt]
  constructor
  · rintro ⟨predecessorSemantic, output, hslot, newEdgeSemantic, hcap⟩
    exact ⟨output,
      by simpa [BoundedCarrierBoolLiveSlot, BoundedCarrierLiveSlot] using hslot,
      predecessorSemantic, newEdgeSemantic,
      (outputCapBool_ofGraphFamilyCode_eq state code edgeState
        predecessorSemantic output newEdgeSemantic).symm.trans hcap⟩
  · rintro ⟨output, hslot, predecessorSemantic, newEdgeSemantic, hcap⟩
    refine ⟨predecessorSemantic, output, ?_, newEdgeSemantic, ?_⟩
    · simpa [BoundedCarrierBoolLiveSlot, BoundedCarrierLiveSlot] using hslot
    · rw [outputCapBool_ofGraphFamilyCode_eq state code edgeState
        predecessorSemantic output newEdgeSemantic]
      exact hcap

end GoertzelV24ClosedWebLocalLayerSerialCellFiniteCapReflection

end Mettapedia.GraphTheory.FourColor
