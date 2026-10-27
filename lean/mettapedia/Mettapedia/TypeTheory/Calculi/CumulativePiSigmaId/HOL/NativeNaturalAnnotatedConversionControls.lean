import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedControls

/-!
# Original natural rows composed with typed beta

The zero row runs in its original open dependent telescope. A beta identity
at that same dependent result type joins it to a distinct annotated endpoint.
The successor row is retained independently. Disabling a row refuses its
declared-step evidence, while beta remains available.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.Controls

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies

def operations := AnnotatedControls.operations
abbrev Const := AnnotatedControls.Const
abbrev resultLevel : Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat := .max (.param 0) (.param 1)

def profile : Programs.ComputationProfiles.Selection := fun _ => true

def canonical (row : Row) :
    Instance operations profile row (row.parameters operations) (row.context operations) where
  contextFormed := by
    cases row with
    | zero => exact Programs.Annotated.context_formed profile ⟨0, by decide⟩
    | successor => exact Programs.Annotated.context_formed profile ⟨1, by decide⟩
  sourceSubstitution := CTm.ids
  targetSubstitution := HOL.Subst.id
  typed := by
    intro index
    rw [CTm.subst_ids]
    exact .var index
  represented := fun index => .var index

def zeroInstance := canonical .zero
def successorInstance := canonical .successor

def zeroStep : Step operations profile profile zeroInstance.source zeroInstance.target :=
  .row zeroInstance rfl rfl

def successorStep : Step operations profile profile successorInstance.source successorInstance.target :=
  .row successorInstance rfl rfl

theorem successor_free : successorStep.proof.FunctionExtensionalityFree := successorStep.proof_free

theorem zero_source_equal : CEqual (Programs.Annotated.church profile)
    zeroInstance.index.sourceContext zeroInstance.source.term zeroInstance.target.term
    zeroInstance.index.sourceType := zeroInstance.source_equal rfl

theorem result_formed : CTyped (Programs.Annotated.church profile)
    (Row.zero.context operations) (Row.zero.type operations) (.head (.sort resultLevel)) := by
  change CTyped (Programs.Annotated.church profile) (Row.zero.context operations)
    (.app (.var ⟨2, by decide⟩) (.const zeroName)) (.head (.sort resultLevel))
  have family : CTyped (Programs.Annotated.church profile) (Row.zero.context operations)
      (.var ⟨2, by decide⟩) (.pi (.const natName) (.head (.sort resultLevel))) := by
    have shape : (Row.zero.context operations).lookup (⟨2, by decide⟩ : Fin 3) =
        CTm.pi (.const natName) (.head (.sort resultLevel)) := by rfl
    rw [← shape]
    exact CDerivable.var (P := Programs.Annotated.church profile)
      (Γ := Row.zero.context operations) (⟨2, by decide⟩ : Fin 3)
  exact CDerivable.appElim family (Programs.Annotated.Functions.zero_typed profile)

def identityBeta : BetaInstance operations profile operations.parameters (Row.zero.context operations) where
  contextFormed := zeroInstance.contextFormed
  domain := Row.zero.type operations
  body := .var 0
  argument := zeroInstance.target.term
  family := (Row.zero.type operations).rename wk
  domainLevel := .sort resultLevel
  productLevel := .sort (.max resultLevel resultLevel)
  domainUniverse := .sort _
  productUniverse := .sort _
  domainTyped := result_formed
  productTyped := .piForm result_formed (.sort _) result_formed.weaken (.sort _) (.sorts _ _)
  bodyTyped := .var 0
  argumentTyped := zeroInstance.target.typed
  domainCarrier := operations.result
  resultCarrier := operations.result
  domainCode := .app (.var (.vs (.vs .vz))) (HOL.weakenCtx operations.parameters operations.zero)
  bodyCode := .var .vz
  argumentCode := zeroInstance.target.code
  domainReading := by
    change AnnotatedReads operations (Γ := operations.parameters)
      (.app (.var ⟨2, by decide⟩) (.const zeroName)) _
    exact .application (AnnotatedReads.var (Γ := operations.parameters) (.vs (.vs .vz))) .zero
  bodyReading := AnnotatedReads.var (Γ := operations.result :: operations.parameters) .vz
  argumentReading := zeroInstance.target.reading

theorem middle_state : identityBeta.target = zeroInstance.target :=
  State.ext _ _ rfl

def betaStep : Step operations profile profile identityBeta.source zeroInstance.target :=
  middle_state ▸ Step.beta identityBeta

def mixedPath : (bubbles operations profile).Conv profile zeroInstance.source identityBeta.source :=
  .trans (.step zeroStep) (.symm (.step betaStep))

theorem mixed_source_equal : CEqual (Programs.Annotated.church profile)
    zeroInstance.index.sourceContext zeroInstance.source.term identityBeta.source.term
    zeroInstance.index.sourceType := source_equal mixedPath

def mixedProof : HOL.ProofSyntax Const (assumptions operations operations.parameters)
    (.eq zeroInstance.source.code identityBeta.source.code) := elaborate mixedPath

theorem mixed_free : mixedProof.FunctionExtensionalityFree := elaborate_free mixedPath

theorem mixed_work : BubbleElaboration.stepCount mixedPath = 2 := by
  simp only [mixedPath, BubbleElaboration.stepCount_trans, BubbleElaboration.stepCount_symm,
    BubbleElaboration.stepCount_step]

theorem endpoints_differ : zeroInstance.source.term ≠ identityBeta.source.term := by
  intro same
  cases same

theorem disabled_zero_step_refused :
    ¬ Nonempty (Step operations profile (fun _ => false) zeroInstance.source zeroInstance.target) := by
  rintro ⟨step⟩
  obtain ⟨domain, body, argument, same⟩ := step.disabled_source_is_beta
  cases same

def betaWithoutRows : Step operations profile (fun _ => false) identityBeta.source zeroInstance.target :=
  middle_state ▸ Step.beta identityBeta

theorem widening_beta_preserves_proof :
    elaborate ((bubbles operations profile).widen
      (Step.widen (large := profile) (fun _ impossible => Bool.noConfusion impossible)) (.step betaWithoutRows)) =
      elaborate (.step betaWithoutRows) :=
  elaborate_widen (large := profile) (fun _ impossible => Bool.noConfusion impossible) (.step betaWithoutRows)

#print axioms result_formed
#print axioms mixed_source_equal
#print axioms mixedProof
#print axioms mixed_free
#print axioms middle_state
#print axioms widening_beta_preserves_proof

end AnnotatedConversion.Controls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
