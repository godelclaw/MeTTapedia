import Mettapedia.Languages.Megalodon.HOLTermEncoding
import Mettapedia.Logic.HOL.BetaEtaSubstitution
import Mettapedia.Logic.HOL.BetaEtaConfluence
import Mettapedia.Languages.Megalodon.NormalizationNormalForm

/-!
# Conversion preservation by Megalodon's complete HOL term encoding

Both stages of the existing encoding preserve typed beta and eta steps.
Consequently, the full encoding preserves conversion in every typed context,
independently of a model or checker budget. Reflection is deliberately
separate: primitive truth and its quantified encoding have identical images
while remaining distinct source beta/eta normal forms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLTermConversion

open Mettapedia.Logic.HOL
open EtaConversion HOLTermEncoding HenkinEqualityInterpretation ImpredicativeConnectives

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma : Ctx Base} {type : Ty Base}

theorem expandEquality_instantiate {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result) :
    expandEquality (instantiate argument body) =
      instantiate (expandEquality argument) (expandEquality body) := by
  unfold instantiate
  rw [expandEquality_subst]
  apply subst_ext
  intro type index
  cases index <;> rfl

theorem expandEquality_beta {source target : Term Const gamma type}
    (reduced : BetaNormalization.Reduces source target) :
    BetaNormalization.Reduces (expandEquality source) (expandEquality target) := by
  obtain ⟨step⟩ := reduced
  induction step with
  | beta body argument =>
      simpa only [expandEquality, expandEquality_instantiate, BetaNormalization.Reduces] using
        (⟨ContextualTrinity.BetaStep.beta (expandEquality body) (expandEquality argument)⟩ :
          BetaNormalization.Reduces _ _)
  | appFun _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.appFun _ step⟩
  | appArg _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.appArg _ step⟩
  | lam _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.lam step⟩
  | andLeft _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.andLeft _ step⟩
  | andRight _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.andRight _ step⟩
  | orLeft _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.orLeft _ step⟩
  | orRight _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.orRight _ step⟩
  | impLeft _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.impLeft _ step⟩
  | impRight _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.impRight _ step⟩
  | not _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.not step⟩
  | eqLeft _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.appFun _ (.appArg _ step)⟩
  | eqRight _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.appArg _ step⟩
  | all _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.all step⟩
  | ex _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.ex step⟩

theorem expandEquality_eta {source target : Term Const gamma type} (step : EtaStep source target) :
    EtaStep (expandEquality source) (expandEquality target) := by
  induction step with
  | eta function =>
      simpa only [expandEquality, weaken, expandEquality_rename] using
        EtaStep.eta (expandEquality function)
  | appFun _ _ ih => exact .appFun _ ih
  | appArg _ _ ih => exact .appArg _ ih
  | lam _ ih => exact .lam ih
  | andLeft _ _ ih => exact .andLeft _ ih
  | andRight _ _ ih => exact .andRight _ ih
  | orLeft _ _ ih => exact .orLeft _ ih
  | orRight _ _ ih => exact .orRight _ ih
  | impLeft _ _ ih => exact .impLeft _ ih
  | impRight _ _ ih => exact .impRight _ ih
  | not _ ih => exact .not ih
  | eqLeft _ _ ih => exact .appFun _ (.appArg _ ih)
  | eqRight _ _ ih => exact .appArg _ ih
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih

theorem expandInline_beta {source target : Term Const gamma type}
    (reduced : BetaNormalization.Reduces source target) :
    BetaNormalization.Reduces (expandInline source) (expandInline target) := by
  obtain ⟨step⟩ := reduced
  induction step with
  | beta body argument =>
      simpa only [expandInline, expandInline_instantiate, BetaNormalization.Reduces] using
        (⟨ContextualTrinity.BetaStep.beta (expandInline body) (expandInline argument)⟩ :
          BetaNormalization.Reduces _ _)
  | appFun _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.appFun _ step⟩
  | appArg _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.appArg _ step⟩
  | lam _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.lam step⟩
  | impLeft _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.impLeft _ step⟩
  | impRight _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.impRight _ step⟩
  | not _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.impLeft _ step⟩
  | eqLeft _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.eqLeft _ step⟩
  | eqRight _ _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.eqRight _ step⟩
  | all _ ih =>
      obtain ⟨step⟩ := ih
      exact ⟨.all step⟩
  | andLeft _ _ ih =>
      obtain ⟨step⟩ := BetaNormalization.reduces_rename (Rename.weaken (σ := .prop)) ih
      exact ⟨.all (.impLeft _ (.impLeft _ step))⟩
  | andRight _ _ ih =>
      obtain ⟨step⟩ := BetaNormalization.reduces_rename (Rename.weaken (σ := .prop)) ih
      exact ⟨.all (.impLeft _ (.impRight _ (.impLeft _ step)))⟩
  | orLeft _ _ ih =>
      obtain ⟨step⟩ := BetaNormalization.reduces_rename (Rename.weaken (σ := .prop)) ih
      exact ⟨.all (.impLeft _ (.impLeft _ step))⟩
  | orRight _ _ ih =>
      obtain ⟨step⟩ := BetaNormalization.reduces_rename (Rename.weaken (σ := .prop)) ih
      exact ⟨.all (.impRight _ (.impLeft _ (.impLeft _ step)))⟩
  | ex _ ih =>
      obtain ⟨step⟩ := BetaNormalization.reduces_rename (Rename.lift (Rename.weaken (σ := .prop))) ih
      exact ⟨.all (.impLeft _ (.all (.impLeft _ step)))⟩

theorem expandInline_eta {source target : Term Const gamma type} (step : EtaStep source target) :
    EtaStep (expandInline source) (expandInline target) := by
  induction step with
  | eta function =>
      simpa only [expandInline, weaken, expandInline_rename] using
        EtaStep.eta (expandInline function)
  | appFun _ _ ih => exact .appFun _ ih
  | appArg _ _ ih => exact .appArg _ ih
  | lam _ ih => exact .lam ih
  | impLeft _ _ ih => exact .impLeft _ ih
  | impRight _ _ ih => exact .impRight _ ih
  | not _ ih => exact .impLeft _ ih
  | eqLeft _ _ ih => exact .eqLeft _ ih
  | eqRight _ _ ih => exact .eqRight _ ih
  | all _ ih => exact .all ih
  | andLeft _ _ ih =>
      have step := EtaNormalization.rename_step (Rename.weaken (σ := .prop)) ih
      exact .all (.impLeft _ (.impLeft _ step))
  | andRight _ _ ih =>
      have step := EtaNormalization.rename_step (Rename.weaken (σ := .prop)) ih
      exact .all (.impLeft _ (.impRight _ (.impLeft _ step)))
  | orLeft _ _ ih =>
      have step := EtaNormalization.rename_step (Rename.weaken (σ := .prop)) ih
      exact .all (.impLeft _ (.impLeft _ step))
  | orRight _ _ ih =>
      have step := EtaNormalization.rename_step (Rename.weaken (σ := .prop)) ih
      exact .all (.impRight _ (.impLeft _ (.impLeft _ step)))
  | ex _ ih =>
      have step := EtaNormalization.rename_step (Rename.lift (Rename.weaken (σ := .prop))) ih
      exact .all (.impLeft _ (.all (.impLeft _ step)))

theorem encode_step {source target : Term Const gamma type} (step : BetaEtaStep source target) :
    BetaEtaStep (encode source) (encode target) := by
  rcases step with beta | eta
  · exact Or.inl (expandInline_beta (expandEquality_beta beta))
  · exact Or.inr (expandInline_eta (expandEquality_eta eta))

theorem encode_conversion {source target : Term Const gamma type}
    (converted : BetaEtaConv source target) : BetaEtaConv (encode source) (encode target) :=
  BetaEtaSubstitution.map encode (fun step => encode_step step) converted

/-- Primitive truth and quantified truth are distinct source normal forms.
Their logical equivalence does not make them beta/eta convertible. -/
theorem primitive_truth_not_convertible :
    ¬ BetaEtaConv (Term.top : Formula Const gamma) truth := by
  have topNormal : Mettapedia.Logic.Relation.IsNormal BetaEtaStep
      (Term.top : Formula Const gamma) := by
    intro target step
    rcases step with beta | eta
    · obtain ⟨beta⟩ := beta
      cases beta
    · cases eta
  have truthNormal : Mettapedia.Logic.Relation.IsNormal BetaEtaStep
      (truth : Formula Const gamma) := by
    intro target step
    rcases step with beta | eta
    · obtain ⟨beta⟩ := beta
      cases beta with
      | all inner =>
          cases inner with
          | impLeft _ inner => cases inner
          | impRight _ inner => cases inner
    · cases eta with
      | all inner =>
          cases inner with
          | impLeft _ inner => cases inner
          | impRight _ inner => cases inner
  intro converted
  have same := BetaEtaConfluence.normal_eq_of_convertible topNormal truthNormal converted
  cases same

/-- The full encoding preserves conversion but does not reflect it. -/
theorem same_encoding_does_not_reflect_conversion :
    encode (Term.top : Formula Const gamma) = encode truth ∧
      ¬ BetaEtaConv (Term.top : Formula Const gamma) truth :=
  ⟨rfl, primitive_truth_not_convertible⟩

section Native

open MathdataKernel HenkinTermInterpretation

variable {environment : Environment} {gamma : Ctx HenkinTermInterpretation.Base}
  {type : Ty HenkinTermInterpretation.Base}

/-- Native beta/eta runs on encoded source-convertible terms return the same
raw result, even when their successful budgets differ. -/
theorem native_normalization_coherent (left right : Term (Constant environment) gamma type)
    {leftFuel rightFuel : Nat} {leftOutput rightOutput : Tm}
    (converted : BetaEtaConv left right)
    (leftAccepted : Tm.normalize leftFuel (native left) = some leftOutput)
    (rightAccepted : Tm.normalize rightFuel (native right) = some rightOutput) :
    leftOutput = rightOutput :=
  NormalizationNormalForm.normalize_coherent (encode left) (encode right)
    (native_erased left) (native_erased right) (encode_conversion converted)
    leftAccepted rightAccepted

/-- The actual delta/beta/eta pipeline has the same coherence when neither
input contains an expandable declaration. -/
theorem native_opaque_coherent (left right : Term (Constant environment) gamma type)
    {leftFuel rightFuel : Nat} {leftOutput rightOutput : Tm}
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (converted : BetaEtaConv left right)
    (leftAccepted : MathdataKernel.normalize environment leftFuel (native left) = some leftOutput)
    (rightAccepted : MathdataKernel.normalize environment rightFuel (native right) = some rightOutput) :
    leftOutput = rightOutput := by
  apply native_normalization_coherent left right converted
  · simpa [MathdataKernel.normalize, DeltaNormalInvariant.fixed leftNormal]
      using leftAccepted
  · simpa [MathdataKernel.normalize, DeltaNormalInvariant.fixed rightNormal]
      using rightAccepted

/-- The executable decision preserves source conversion, with the encoded
grammar as its checked input. -/
theorem native_conversion_preserved (left right : Term (Constant environment) gamma type)
    (converted : BetaEtaConv left right) :
    NormalizationNormalForm.decideConversion (encode left) (encode right)
      (native_erased left) (native_erased right) = true :=
  (NormalizationNormalForm.decideConversion_correct _ _ _ _).mpr (encode_conversion converted)

/-- Acceptance of the encoded equality still does not identify source
presentations: truth supplies an actual executable-decision counterexample. -/
theorem native_decision_does_not_reflect_source :
    NormalizationNormalForm.decideConversion
        (encode (Term.top : Formula (Constant environment) gamma)) (encode truth)
        (native_erased .top) (native_erased truth) = true ∧
      ¬ BetaEtaConv (Term.top : Formula (Constant environment) gamma) truth := by
  refine ⟨?_, primitive_truth_not_convertible⟩
  apply (NormalizationNormalForm.decideConversion_correct _ _ _ _).mpr
  exact .refl _

end Native

#print axioms expandEquality_beta
#print axioms expandEquality_eta
#print axioms expandInline_beta
#print axioms expandInline_eta
#print axioms encode_step
#print axioms encode_conversion
#print axioms same_encoding_does_not_reflect_conversion
#print axioms native_normalization_coherent
#print axioms native_opaque_coherent
#print axioms native_conversion_preserved
#print axioms native_decision_does_not_reflect_source

end Mettapedia.Languages.Megalodon.HOLTermConversion
