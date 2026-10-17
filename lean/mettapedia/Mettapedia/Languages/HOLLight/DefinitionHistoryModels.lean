import Mettapedia.Languages.HOLLight.ModelInterpretation

/-!
# Models for admitted polymorphic constant-definition histories

A history retains each original source admission receipt and its actual
registered successor context. Its model is constructed incrementally using
the existing polymorphic source extension. Earlier declarations, open-term
denotations and truths survive every later fresh definition. Each admitted
defining equation remains true at every legitimate type instance.

These histories contain constant definitions. The existing carrier-changing
type-definition construction requires additional signature transport to join
mixed source histories; it is not represented by a constant update.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.DefinitionHistoryModels

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open DefinitionAdapters SignatureFormation ModelInterpretation

universe w

/-- Chronological evidence for the original admission operation. No additional
checker or declaration policy is introduced. -/
inductive ConstantHistory (initial : TheoryContext) : TheoryContext → Type where
  | nil : ConstantHistory initial initial
  | snoc {prior : TheoryContext} (history : ConstantHistory initial prior)
      (instances : InstanceWitnesses) (name : Name) (source : SourceTerm)
      (result : ContextConstantDefinitionResult)
      (accepted : admitConstantInTheory prior instances name source = some result) :
      ConstantHistory initial result.context

namespace ConstantHistory

variable {initial final : TheoryContext}

def records : {final : TheoryContext} → ConstantHistory initial final →
    List ContextConstantDefinitionResult
  | _, .nil => []
  | _, .snoc prior _ _ _ result _ => prior.records ++ [result]

theorem includes (history : ConstantHistory initial final) :
    initial.signature.Includes final.signature := by
  induction history with
  | nil => exact Signature.Includes.refl _
  | snoc prior instances name source result accepted ih =>
      exact ih.trans (admitConstantInTheory_result accepted).2.2.1

theorem record_registered (history : ConstantHistory initial final)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records) :
    final.signature.constants result.output.constant = some result.definition.ty := by
  induction history with
  | nil => simp [records] at member
  | snoc prior instances name source added accepted ih =>
      rw [records, List.mem_append, List.mem_singleton] at member
      rcases member with earlier | rfl
      · exact (admitConstantInTheory_result accepted).2.2.1.2 _ _ (ih earlier)
      · exact (admitConstantInTheory_result accepted).2.2.2.2.2.1

theorem record_body_formed (history : ConstantHistory initial final)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records) :
    AnnotationsFormed final.signature result.definition.term := by
  induction history with
  | nil => simp [records] at member
  | snoc prior instances name source added accepted ih =>
      rw [records, List.mem_append, List.mem_singleton] at member
      rcases member with earlier | rfl
      · exact (ih earlier).mono (admitConstantInTheory_result accepted).2.2.1
      · exact ((checkSource_sound _ _ (admitConstantInTheory_result accepted).1).2).mono
          (admitConstantInTheory_result accepted).2.2.1

theorem record_equation_shape (history : ConstantHistory initial final)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records) :
    result.output.definitionTheorem.sequent.concl.term =
      CanonicalTerm.equalityDB result.definition.ty
        (.const result.output.constant result.definition.ty) result.definition.term := by
  induction history with
  | nil => simp [records] at member
  | snoc prior instances name source added accepted ih =>
      rw [records, List.mem_append, List.mem_singleton] at member
      rcases member with earlier | rfl
      · exact ih earlier
      · exact (ConstantAdmission.source_equation accepted).2.2

theorem record_equation_boolean (history : ConstantHistory initial final)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records) :
    result.output.definitionTheorem.sequent.concl.IsBool := by
  induction history with
  | nil => simp [records] at member
  | snoc prior instances name source added accepted ih =>
      rw [records, List.mem_append, List.mem_singleton] at member
      rcases member with earlier | rfl
      · exact ih earlier
      · exact (ConstantAdmission.source_equation accepted).2.resultIsBool

/-- The model follows the actual source contexts and checked bodies. Every
public instance of one declaration is interpreted by the same extension. -/
noncomputable def extendModel {final : TheoryContext} (history : ConstantHistory initial final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  match history with
  | .nil => model
  | .snoc prior _ _ _ result _ =>
      ConstantAdmission.sourceExtension result (prior.extendModel model)

theorem carrier (history : ConstantHistory initial final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (history.extendModel model).Carrier = model.Carrier := by
  induction history with
  | nil => rfl
  | snoc prior instances name source result accepted ih => exact ih

theorem fullDomains (history : ConstantHistory initial final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : model.FullDomains) :
    (history.extendModel model).FullDomains := by
  induction history with
  | nil => exact full
  | snoc prior instances name source result accepted ih =>
      exact ConstantAdmission.sourceExtension_fullDomains result _ ih

theorem functionsRespectEqv (history : ConstantHistory initial final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (extensional : model.FunctionsRespectEqv) :
    (history.extendModel model).FunctionsRespectEqv := by
  induction history with
  | nil => exact extensional
  | snoc prior instances name source result accepted ih =>
      change (ConstantAdmission.sourceExtension result _).FunctionsRespectEqv
      rw [ConstantAdmission.sourceExtension_eq_reduct]
      exact (HOL.HenkinModel.constantSubstitutionReduct_functionsRespectEqv_iff
        (ConstantAdmission.sourceExpansion result) _).mpr ih

noncomputable def extendValuation {final : TheoryContext} (history : ConstantHistory initial final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) {context : HOL.Ctx AtomicTy}
    (valuation : model.Valuation context) : (history.extendModel model).Valuation context :=
  match history with
  | .nil => valuation
  | .snoc prior _ _ _ _ _ => prior.extendValuation model valuation

/-- Formation establishes that every future fresh declaration is absent
from the original term. Bindings and open valuations are retained. -/
theorem denote_old (history : ConstantHistory initial final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type}
    (formed : AnnotationsFormed initial.signature term)
    (translated : TranslatesCompositionally context term type target)
    (valuation : model.Valuation context) :
    HEq ((history.extendModel model).denote target (history.extendValuation model valuation))
      (model.denote target valuation) := by
  induction history with
  | nil => rfl
  | snoc prior instances name source result accepted ih =>
      have omitted := (formed.mono prior.includes).omits_unregistered
        (ConstantAdmission.admitted_identity_fresh accepted)
      exact (heq_of_eq (ConstantAdmission.sourceExtension_preserves_translation result _
        translated omitted (prior.extendValuation model valuation))).trans ih

theorem models_old (history : ConstantHistory initial final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (formed : AnnotationsFormed initial.signature term)
    (translated : TranslatesCompositionally [] term .prop formula) :
    (history.extendModel model).models formula ↔ model.models formula := by
  induction history with
  | nil => rfl
  | snoc prior instances name source result accepted ih =>
      exact (ConstantAdmission.sourceExtension_preserves_old_truth accepted _
        (formed.mono prior.includes) translated).trans ih

private theorem equation_omits_fresh (history : ConstantHistory initial final)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records)
    {instances : InstanceWitnesses} {name : Name} {source : SourceTerm}
    {added : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory final instances name source = some added) :
    result.output.definitionTheorem.sequent.concl.term.OmitsConstant added.output.constant := by
  have fresh := ConstantAdmission.admitted_identity_fresh accepted
  have bodyOmitted := (history.record_body_formed member).omits_unregistered fresh
  have different : result.output.constant ≠ added.output.constant := by
    intro equal
    have registered := history.record_registered member
    rw [equal, fresh] at registered
    cases registered
  have equalityDifferent : Const.equality ≠ added.output.constant := by
    rw [(ConstantAdmission.source_equation accepted).1]
    intro equal
    have origins := (Const.mk.inj equal).2
    cases origins
  rw [history.record_equation_shape member]
  exact ⟨⟨equalityDifferent, different⟩, bodyOmitted⟩

/-- Every earlier equation remains true after subsequent admissions. The
source output is used directly, at arbitrary simultaneous type instances. -/
theorem models_record_equation (history : ConstantHistory initial final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records)
    (substitution : TypeSubst) {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.definitionTheorem.sequent.concl.term)
      .prop formula) :
    (history.extendModel model).models formula := by
  induction history with
  | nil => simp [records] at member
  | snoc prior instances name source added accepted ih =>
      rw [records, List.mem_append, List.mem_singleton] at member
      rcases member with earlier | rfl
      · have omitted := (equation_omits_fresh prior earlier accepted).typeInstance substitution
        have preserved :
            (ConstantAdmission.sourceExtension added (prior.extendModel model)).models formula ↔
              (prior.extendModel model).models formula := by
          rw [ConstantAdmission.sourceExtension_eq_reduct]
          rw [← (prior.extendModel model).models_substConst]
          rw [ConstantAdmission.sourceExpansion_preserves_translation added translated omitted]
        exact preserved.mpr (ih earlier)
      · exact ConstantAdmission.sourceExtension_models_source_equation accepted (prior.extendModel model)
          substitution translated

/-- Actual admission supplies a translated Boolean equation at every type
instance; the meaning theorem is not vacuous on absent translations. -/
theorem record_equation_meaning (history : ConstantHistory initial final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records)
    (substitution : TypeSubst) :
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB result.output.definitionTheorem.sequent.concl.term)
        .prop formula ∧ (history.extendModel model).models formula := by
  let instantiated := (TypeCorrectTermSubstitution.ofTypes substitution).apply
    result.output.definitionTheorem.sequent.concl
  have boolean : instantiated.IsBool := by
    change substitution.apply result.output.definitionTheorem.sequent.concl.ty = Ty.bool
    rw [show result.output.definitionTheorem.sequent.concl.ty = Ty.bool from
      history.record_equation_boolean member, TypeSubst.apply_bool]
  obtain ⟨formula, translated⟩ := CanonicalTerm.exists_formula boolean
  exact ⟨formula, translated, history.models_record_equation model member substitution translated⟩

/-- Join chronological source receipts without rechecking or changing their
original registration contexts. -/
def append {middle final : TheoryContext} (first : ConstantHistory initial middle) :
    ConstantHistory middle final → ConstantHistory initial final
  | .nil => first
  | .snoc prior instances name source result accepted =>
      .snoc (first.append prior) instances name source result accepted

theorem records_append {middle : TheoryContext} (first : ConstantHistory initial middle)
    (second : ConstantHistory middle final) :
    (first.append second).records = first.records ++ second.records := by
  induction second with
  | nil => simp [append, records]
  | snoc prior instances name source result accepted ih =>
      simp only [append, records, ih, List.append_assoc]

theorem model_append {middle : TheoryContext} (first : ConstantHistory initial middle)
    (second : ConstantHistory middle final)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (first.append second).extendModel model = second.extendModel (first.extendModel model) := by
  induction second with
  | nil => rfl
  | snoc prior instances name source result accepted ih =>
      simp only [append, extendModel, ih]

end ConstantHistory

namespace Controls

open DefinitionAdapters.ContextControls

/-- The first receipt is supplied by the original registered admission gate. -/
def identityResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory baseContext certificates (Name.global "identity")
    DefinitionAdapters.Controls.identitySource).get identity_definition_admitted

theorem identity_admitted :
    admitConstantInTheory baseContext certificates (Name.global "identity")
      DefinitionAdapters.Controls.identitySource = some identityResult :=
  (Option.some_get identity_definition_admitted).symm

def identityHistory : ConstantHistory baseContext identityResult.context :=
  .snoc .nil certificates (Name.global "identity") DefinitionAdapters.Controls.identitySource
    identityResult identity_admitted

/-- A later checked source body refers to the actual older definition identity. -/
def aliasBody : SourceTerm :=
  .const identityResult.output.constant identityResult.definition.ty

theorem alias_admission :
    (admitConstantInTheory identityResult.context certificates (Name.global "alias")
      aliasBody).isSome = true := by
  decide +kernel

def aliasResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory identityResult.context certificates (Name.global "alias")
    aliasBody).get alias_admission

theorem alias_admitted :
    admitConstantInTheory identityResult.context certificates (Name.global "alias")
      aliasBody = some aliasResult :=
  (Option.some_get alias_admission).symm

def twoDefinitions : ConstantHistory baseContext aliasResult.context :=
  .snoc identityHistory certificates (Name.global "alias") aliasBody aliasResult alias_admitted

theorem chronological_records :
    twoDefinitions.records = [identityResult, aliasResult] := rfl

/-- Both the old equation and its dependency-bearing successor are true in
one constructed final model, at every public type instance. -/
theorem both_equations (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (result : ContextConstantDefinitionResult)
    (member : result ∈ [identityResult, aliasResult]) (substitution : TypeSubst)
    {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.definitionTheorem.sequent.concl.term)
      .prop formula) :
    (twoDefinitions.extendModel model).models formula :=
  twoDefinitions.models_record_equation model member substitution translated

/-- Reusing a registered source name is refused by the original operation;
it does not add a second meaning to the constructed history. -/
theorem repeated_name_refused :
    admitConstantInTheory aliasResult.context certificates (Name.global "identity")
      DefinitionAdapters.Controls.identitySource = none := by
  apply admitConstantInTheory_repeated_refused
  have registered := twoDefinitions.record_registered
    (result := identityResult) (by simp [chronological_records])
  have actual := aliasResult.context.constantNames _ _ registered
  simpa only [(ConstantAdmission.source_equation identity_admitted).1, constantName] using actual

/-- A separate dependency-bearing control retains a genuine public type
parameter, rather than merely quantifying instances of a monomorphic body. -/
def polymorphicHistory : ConstantHistory coreContext
    ModelInterpretation.Controls.polymorphicIdentityResult.context :=
  .snoc .nil (fun _ _ => ⟨[]⟩) (Name.global "polymorphicIdentity")
    ModelInterpretation.Controls.polymorphicIdentitySource
    ModelInterpretation.Controls.polymorphicIdentityResult
    (Option.some_get ModelInterpretation.Controls.polymorphicIdentity_definition_admitted).symm

def polymorphicAliasBody : SourceTerm :=
  .const ModelInterpretation.Controls.polymorphicIdentityResult.output.constant
    ModelInterpretation.Controls.polymorphicIdentityResult.definition.ty

theorem polymorphic_alias_admission :
    (admitConstantInTheory ModelInterpretation.Controls.polymorphicIdentityResult.context
      certificates (Name.global "polymorphicAlias") polymorphicAliasBody).isSome = true := by
  decide +kernel

def polymorphicAliasResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory ModelInterpretation.Controls.polymorphicIdentityResult.context
    certificates (Name.global "polymorphicAlias") polymorphicAliasBody).get
      polymorphic_alias_admission

def polymorphicDefinitions : ConstantHistory coreContext polymorphicAliasResult.context :=
  .snoc polymorphicHistory certificates (Name.global "polymorphicAlias") polymorphicAliasBody
    polymorphicAliasResult (Option.some_get polymorphic_alias_admission).symm

/-- Both complete source equations have true translations in one constructed
model after their parameter is instantiated to a function type. -/
theorem polymorphic_function_instance :
    ∀ result ∈ [ModelInterpretation.Controls.polymorphicIdentityResult, polymorphicAliasResult],
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally []
          ((TermSubst.mk ModelInterpretation.Controls.functionInstance []).applyDB
            result.output.definitionTheorem.sequent.concl.term) .prop formula ∧
        (polymorphicDefinitions.extendModel ModelInterpretation.Controls.initialModel.{w}).models
          formula := by
  intro result member
  exact polymorphicDefinitions.record_equation_meaning
    ModelInterpretation.Controls.initialModel member ModelInterpretation.Controls.functionInstance

/-- A future identity is unavailable when its defining body is submitted to
an earlier source context, even if its display type is correct. -/
theorem future_reference_refused :
    admitConstantInTheory baseContext certificates (Name.global "future")
      (.const aliasResult.output.constant aliasResult.definition.ty) = none := by
  decide +kernel

end Controls

end Mettapedia.Languages.HOLLight.DefinitionHistoryModels
