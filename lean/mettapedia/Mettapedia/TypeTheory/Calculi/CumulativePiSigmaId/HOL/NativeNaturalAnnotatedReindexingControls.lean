import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedReindexing
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedConversionControls

/-!
# Typed natural callers and exact reindexed proofs

Weakening adds the original natural-index binder. A second caller instantiates
that binder with zero. Both act on real declared rows and on the mixed dependent
beta/natural path. A mismatched HOL successor assignment cannot read the source
zero assignment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.ReindexingControls

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies
open AnnotatedConversion.Controls

def weaken : Substitution operations profile operations.parameters operations.successorParameters
    (Row.zero.context operations) (Row.successor.context operations) where
  targetFormed := successorInstance.contextFormed
  source := fun index => .var index.succ
  target := HOL.Subst.ofRename HOL.Rename.weaken
  typed := by
    intro index
    change CTyped (Programs.Annotated.church profile)
      (.snoc (Row.zero.context operations) (.const natName)) (.var index.succ)
      (CTm.subst (fun index => .var index.succ) ((Row.zero.context operations).lookup index))
    have shift := (CTm.rename_subst wk CTm.ids ((Row.zero.context operations).lookup index)).symm
    simp only [CTm.subst_ids, CTm.ids, CTm.rename, wk] at shift
    rw [shift]
    exact CTyped.weaken (E := .const natName)
      (CDerivable.var (P := Programs.Annotated.church profile) (Γ := Row.zero.context operations) index)
  represented := fun index => AnnotatedReads.var (Γ := operations.successorParameters) (.vs index)

def closeZero : Substitution operations profile operations.successorParameters operations.parameters
    (Row.successor.context operations) (Row.zero.context operations) where
  targetFormed := zeroInstance.contextFormed
  source := CTm.subst0 (.const zeroName)
  target := HOL.Subst.single (HOL.weakenCtx operations.parameters operations.zero)
  typed := CSubstMor.single (Programs.Annotated.Functions.zero_typed profile)
  represented := by
    intro type index
    cases index with
    | vz => exact .zero
    | vs prior => exact .var prior

def weakenedPath := (weaken.fibreMap profile zeroInstance.index.sourceType operations.result).mapConv mixedPath

theorem weakening_natural : elaborate weakenedPath = weaken.proof mixedProof :=
  weaken.elaborate_mapConv mixedPath

theorem weakening_work : BubbleElaboration.stepCount weakenedPath = 2 := by
  rw [weakenedPath, weaken.stepCount_mapConv, mixed_work]

def successorPath := (closeZero.fibreMap profile successorInstance.index.sourceType operations.result).mapConv
  (.step successorStep)

theorem successor_natural : elaborate successorPath = closeZero.proof successorStep.proof := by
  simpa only [successorPath, elaborate, BubbleElaboration.sound_step] using
    closeZero.elaborate_mapConv (type := successorInstance.index.sourceType) (.step successorStep)

theorem successor_step_natural : (closeZero.step successorStep).proof = closeZero.proof successorStep.proof :=
  closeZero.step_proof successorStep

theorem successor_work : BubbleElaboration.stepCount successorPath = 1 := by
  simpa only [successorPath, BubbleElaboration.stepCount_step] using
    closeZero.stepCount_mapConv (type := successorInstance.index.sourceType) (.step successorStep)

theorem successor_displayed_type :
    successorInstance.index.sourceType.subst closeZero.source =
      (CTm.app (.var ⟨2, by decide⟩) (.app (.const succName) (.const zeroName)) : CTm Tower.Head 3) := by
  rfl

theorem weakened_source_equal : CEqual (Programs.Annotated.church profile)
    (Row.successor.context operations) (weaken.state zeroInstance.source).term
    (weaken.state identityBeta.source).term (zeroInstance.index.sourceType.subst weaken.source) :=
  source_equal weakenedPath

theorem successor_source_equal : CEqual (Programs.Annotated.church profile)
    (Row.zero.context operations) (closeZero.state successorInstance.source).term
    (closeZero.state successorInstance.target).term
    (successorInstance.index.sourceType.subst closeZero.source) := source_equal successorPath

def restoredPath := (closeZero.fibreMap profile (zeroInstance.index.sourceType.subst weaken.source)
    operations.result).mapConv weakenedPath

/-- The two real callers cancel on the retained HOL proof, including its
hypothesis occurrences and rule tree. -/
theorem restored_proof : HEq (elaborate restoredPath) mixedProof := by
  rw [restoredPath, closeZero.elaborate_mapConv, weakening_natural]
  refine (HOL.ProofSyntax.castIndices_heq _ _ _).trans ?_
  refine (HOL.ProofSyntax.subst_heq_of_heq closeZero.target
    (assumptions_substitute operations weaken.target).symm rfl
    (HOL.ProofSyntax.castIndices_heq _ _ _)).trans ?_
  exact (HOL.ProofSyntax.subst_subst_heq mixedProof HOL.Subst.id closeZero.target weaken.target
    (fun _ => rfl)).symm.trans (HOL.ProofSyntax.subst_id_heq mixedProof)

theorem restored_work : BubbleElaboration.stepCount restoredPath = 2 := by
  rw [restoredPath, closeZero.stepCount_mapConv, weakening_work]

def zeroOnly : Programs.ComputationProfiles.Selection := fun row => decide (row.val = 0)

def limitedPath : (bubbles operations profile).Conv zeroOnly zeroInstance.source identityBeta.source :=
  .trans (.step (.row zeroInstance rfl rfl))
    (.symm (.step (middle_state ▸ Step.beta identityBeta)))

theorem permissions_and_context :
    elaborate ((weaken.fibreMap profile zeroInstance.index.sourceType operations.result).mapConv
      ((bubbles operations profile).widen (Step.widen (large := profile) (fun _ _ => rfl)) limitedPath)) =
    elaborate ((bubbles operations profile).widen (Step.widen (large := profile) (fun _ _ => rfl))
      ((weaken.fibreMap zeroOnly zeroInstance.index.sourceType operations.result).mapConv limitedPath)) :=
  weaken.elaborate_widen_mapConv (type := zeroInstance.index.sourceType) (large := profile)
    (fun _ _ => rfl) limitedPath

theorem mismatched_assignment_refused :
    ¬ AnnotatedReads operations (Γ := operations.parameters) (.const zeroName)
      (.app (HOL.weakenCtx operations.parameters operations.successor)
        (HOL.weakenCtx operations.parameters operations.zero)) := by
  intro reading
  have same := AnnotatedReading.term_unique reading
    (AnnotatedReads.zero (operations := operations) (Γ := operations.parameters))
  cases same

def openNumber : State operations profile
    ⟨operations.successorParameters, Row.successor.context operations, .const natName, operations.number⟩ where
  contextFormed := successorInstance.contextFormed
  term := .var ⟨0, by decide⟩
  typed := by
    have shape : (Row.successor.context operations).lookup (⟨0, by decide⟩ : Fin 4) =
        CTm.const natName := by rfl
    change CTyped (Programs.Annotated.church profile) (Row.successor.context operations)
      (.var (⟨0, by decide⟩ : Fin 4)) (.const natName)
    rw [← shape]
    exact CDerivable.var (P := Programs.Annotated.church profile)
      (Γ := Row.successor.context operations) (⟨0, by decide⟩ : Fin 4)
  code := .var .vz
  reading := AnnotatedReads.var (Γ := operations.successorParameters) .vz

def closedZero : State operations profile
    ⟨operations.successorParameters, Row.successor.context operations, .const natName, operations.number⟩ where
  contextFormed := successorInstance.contextFormed
  term := .const zeroName
  typed := Programs.Annotated.Functions.zero_typed profile
  code := HOL.weakenCtx operations.successorParameters operations.zero
  reading := .zero

theorem source_states_distinct : openNumber ≠ closedZero := by
  intro same
  have terms := congrArg State.term same
  cases terms

theorem closeZero_collapses_states : closeZero.state openNumber = closeZero.state closedZero :=
  State.ext _ _ rfl

/-- Exact forward transport does not make caller substitution injective. -/
theorem closeZero_not_injective : ¬ Function.Injective
    (closeZero.state (type := .const natName) (carrier := operations.number)) := by
  intro injective
  exact source_states_distinct (injective closeZero_collapses_states)

#print axioms weakening_natural
#print axioms successor_natural
#print axioms successor_step_natural
#print axioms weakening_work
#print axioms successor_displayed_type
#print axioms weakened_source_equal
#print axioms successor_source_equal
#print axioms restored_proof
#print axioms restored_work
#print axioms permissions_and_context
#print axioms mismatched_assignment_refused
#print axioms closeZero_not_injective

end AnnotatedConversion.ReindexingControls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
