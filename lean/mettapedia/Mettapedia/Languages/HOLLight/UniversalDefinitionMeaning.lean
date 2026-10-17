import Mettapedia.Languages.HOLLight.UniversalDefinitionModels
import Mettapedia.Languages.HOLLight.PrimitiveTransport

/-!
# Configured MM0 acceptance in constructed universal HOL histories

The finite policy retains the original declaration rows and their order.
Every type admission may use actual unrestricted configured proofs from the
preceding universal theory. Background closure, row metadata/provability and
model truth are earned by that original chronology and its constructed model.
Acceptance implies the original conclusion's meaning under its hypotheses.
This theorem concerns the source kernel; it does not verify C or OCaml code
or assert an efficient arbitrary reverse proof extraction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.UniversalDefinitionMeaning

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters DefinitionModelFamily UniversalDefinitionHistory
open DefinitionHistoryMeaning (axiomList rowPolicy definition firstOrder)
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)

universe w

private theorem equality_bool {term : CanonicalTerm} {operand : Ty} {left right : DBTerm}
    (shape : term.term = CanonicalTerm.equalityDB operand left right) : term.IsBool := by
  have checked := term.checked
  rw [shape] at checked
  exact (DBTerm.inferType_equalityDB_iff.mp checked).2.2

/-- Every original retained definition row is a valid finite kernel axiom
shape. The Boolean and empty-hypothesis facts follow from actual admission. -/
theorem record_metadata {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (history : History initial final records schemas) {recorded : Theorem} (member : recorded ∈ records) :
    recorded.sequent.hyp = ∅ ∧ recorded.sequent.IsBool := by
  have combine {sequent : Sequent} (empty : sequent.hyp = ∅) (boolean : sequent.concl.IsBool) :
      sequent.hyp = ∅ ∧ sequent.IsBool := by
    refine ⟨empty, boolean, ?_⟩
    intro term member
    rw [empty] at member
    exact absurd member (Finset.notMem_empty _)
  induction history with
  | nil => simp at member
  | constant prior instances name source result accepted ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact ih earlier
      · obtain rfl := List.mem_singleton.mp added
        exact combine (admitConstantInTheory_result accepted).2.2.2.2.2.2.2
          (ConstantAdmission.source_equation accepted).2.resultIsBool
  | typeDefinition prior instances request result accepted existence ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact ih earlier
      · have empty := (UniformTypeDefinitionFamily.admitted_parameter_guards accepted).2.2
        have metadata := admitSourceTypeInTheory_result accepted
        have shape := admitSourceTypeInTheory_pointwise accepted
        rcases List.mem_cons.mp added with rfl | added
        · exact combine (metadata.2.2.2.2.1.trans empty) (equality_bool shape.2.2.2.1)
        · obtain rfl := List.mem_singleton.mp added
          exact combine (metadata.2.2.2.2.2.trans empty) (equality_bool shape.2.2.2.2)

/-- The independently implemented saved-proof checker for this configuration. -/
noncomputable def checker {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (_history : History initial final records schemas) := savedChecker (firstOrder records)

private theorem admitted_rows {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (history : History initial final records schemas) : ∀ sequent ∈ axiomList records,
    sequent.hyp = ∅ ∧ rowPolicy records sequent ∧ sequent.IsBool := by
  intro sequent member
  obtain ⟨recorded, present, rfl⟩ := List.mem_map.mp member
  have metadata := record_metadata history present
  exact ⟨metadata.1, member, metadata.2⟩

private theorem row_provable {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (history : History initial final records schemas) : ∀ sequent ∈ axiomList records,
    TranslatedProvable (schemaBackground schemas) sequent := by
  intro sequent member
  obtain ⟨recorded, present, rfl⟩ := List.mem_map.mp member
  exact UniversalDefinitionHistory.History.record_translated_provable history present

/-- Exact configured hosting remains the original HOL source derivability
statement. No efficiently extracted arbitrary reverse proof is inferred. -/
theorem accepted_iff_derives {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (history : History initial final records schemas) (sequent : Sequent) :
    (∃ certificate, (checker history).check (FirstOrder.renderSequent sequent) certificate = true) ↔
    ∃ out : Theorem, Mettapedia.Logic.Derives (HOLLight.Rule (rowPolicy records)) out ∧ out.sequent = sequent := by
  classical
  exact FirstOrder.savedChecker_exact (definition := definition records) rfl
    (admitted_rows history) (fun _ member => member) (firstOrder records) sequent

/-- Actual original INST_TYPE/INST kernel steps retain acceptance after
an arbitrary validated type-and-term substitution. The result is checked
through exact configured hosting, not through a separately asserted closure. -/
theorem accepted_substitution {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)} (history : History initial final records schemas)
    (substitution : TypeCorrectTermSubstitution) {sequent : Sequent}
    (accepted : ∃ certificate, (checker history).check (FirstOrder.renderSequent sequent) certificate = true) :
    ∃ certificate, (checker history).check (FirstOrder.renderSequent
      ⟨substitution.applyHypotheses sequent.hyp, substitution.apply sequent.concl⟩) certificate = true := by
  obtain ⟨actual, derived, same⟩ := (accepted_iff_derives history sequent).mp accepted
  apply (accepted_iff_derives history _).mpr
  refine ⟨substituteTheorem substitution actual,
    PrimitiveTransport.substitution_derives _ substitution (substituteTheorem_semantics _ _) derived, ?_⟩
  change (⟨substitution.applyHypotheses actual.sequent.hyp, substitution.apply actual.sequent.concl⟩ : Sequent) = _
  rw [same]

/-- Successful configured MM0 checking has truth in the actually constructed
whole-history model. Closure, finite-row proofs and background truth are all
earned; only the original conclusion's hypotheses remain a logical premise. -/
theorem accepted_models {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (history : History initial final records schemas) (primitives : Primitives initial)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {sequent : Sequent} {certificate : SavedCertificate}
    (accepted : (checker history).check (FirstOrder.renderSequent sequent) certificate = true) :
    ∃ formula, Translates [] sequent.concl.term .prop formula ∧
      ((∀ hypothesis ∈ translatedHypotheses sequent.hyp,
          (UniversalDefinitionModels.model primitives history other assignment).models hypothesis) →
        (UniversalDefinitionModels.model primitives history other assignment).models formula) := by
  classical
  exact MM0Meaning.accepted_models (definition := definition records) rfl (admitted_rows history)
    (fun _ member => member) (firstOrder records)
    (UniversalDefinitionHistory.History.background_closed history primitives) (row_provable history) accepted
    (UniversalDefinitionModels.model primitives history other assignment)
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _
      (UniversalDefinitionModels.fullDomains primitives history other assignment))
    (UniversalDefinitionModels.models_background primitives history other assignment)

/-- An independent original formula translation fixes the actual meaning
of the conclusion rather than interpreting an encoded proof predicate. -/
theorem accepted_models_of_translation {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (history : History initial final records schemas) (primitives : Primitives initial)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {sequent : Sequent} {certificate : SavedCertificate}
    (accepted : (checker history).check (FirstOrder.renderSequent sequent) certificate = true)
    {formula : HOL.ClosedFormula Symbol} (translation : Translates [] sequent.concl.term .prop formula)
    (hypotheses : ∀ hypothesis ∈ translatedHypotheses sequent.hyp,
      (UniversalDefinitionModels.model primitives history other assignment).models hypothesis) :
    (UniversalDefinitionModels.model primitives history other assignment).models formula := by
  obtain ⟨actual, translated, sound⟩ := accepted_models history primitives other assignment accepted
  cases Translates.unique_eq translated translation
  exact sound hypotheses

/-- A falsified original conclusion cannot have an accepted MM0 certificate
for this actual finite configured history. Execution exhaustion is not used
as a refusal witness. -/
theorem refused_of_false_conclusion {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (history : History initial final records schemas) (primitives : Primitives initial)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (sequent : Sequent) {formula : HOL.ClosedFormula Symbol}
    (translation : Translates [] sequent.concl.term .prop formula)
    (hypotheses : ∀ hypothesis ∈ translatedHypotheses sequent.hyp,
      (UniversalDefinitionModels.model primitives history other assignment).models hypothesis)
    (falseConclusion : ¬ (UniversalDefinitionModels.model primitives history other assignment).models formula)
    (certificate : SavedCertificate) :
    (checker history).check (FirstOrder.renderSequent sequent) certificate = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  exact falseConclusion (accepted_models_of_translation history primitives other assignment accepted translation hypotheses)

/-- Primitive falsity remains false in the actual full-domain history model. -/
theorem model_refuses_falsity {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (history : History initial final records schemas) (primitives : Primitives initial)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ¬ (UniversalDefinitionModels.model primitives history other assignment).models PrimitiveSentences.falsityFormula := by
  intro holds
  have atFalse := holds (ULift.up False)
    (UniversalDefinitionModels.fullDomains primitives history other assignment .prop (ULift.up False))
  exact atFalse.mpr fun _ _ => Iff.rfl

/-- No saved MM0 certificate can establish primitive falsity in this
configured theory, including histories containing actual type definitions. -/
theorem falsity_refused {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)}
    (history : History initial final records schemas) (primitives : Primitives initial)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (certificate : SavedCertificate) :
    (checker history).check (FirstOrder.renderSequent ⟨∅, falsity⟩) certificate = false := by
  apply refused_of_false_conclusion history primitives other assignment ⟨∅, falsity⟩
    PrimitiveSentences.falsityDB_translates _ (model_refuses_falsity history primitives other assignment) certificate
  rintro hypothesis ⟨term, member, _⟩
  exact absurd member (Finset.notMem_empty _)

namespace Controls

open MixedDefinitionModels.Controls MixedDefinitionModelFamily.Controls
open UniversalDefinitionHistory.Controls

theorem late_row_metadata : afterTwoTypesResult.output.definitionTheorem.sequent.hyp = ∅ ∧
    afterTwoTypesResult.output.definitionTheorem.sequent.IsBool :=
  record_metadata originalMixed (List.mem_append_right _ List.mem_cons_self)

theorem late_original_row_acceptance :
    ∃ certificate, (checker originalMixed).check
      (FirstOrder.renderSequent afterTwoTypesResult.output.definitionTheorem.sequent) certificate = true := by
  apply (accepted_iff_derives originalMixed _).mpr
  refine ⟨DefinitionHistorySchemas.Controls.lastRowAxiom, ?_, rfl⟩
  apply Mettapedia.Logic.Derives.least _ _ DefinitionHistorySchemas.Controls.lastRow_derived
  intro premises out step children
  apply Mettapedia.Logic.Derives.node premises out _ children
  rcases step with inference | ⟨sequent, shape, empty, authorized, semantics⟩
  · exact Or.inl inference
  · exact Or.inr ⟨sequent, shape, empty, by
      change sequent = afterTwoTypesResult.output.definitionTheorem.sequent at authorized
      rw [authorized]
      exact List.mem_map.mpr ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩, semantics⟩

def boolInstance : TypeCorrectTermSubstitution :=
  TypeCorrectTermSubstitution.ofTypes ⟨[(TypeFamilySemantics.Controls.alpha, Ty.bool)]⟩

theorem type_instantiation_changes_original_goal :
    boolInstance.apply afterTwoTypesResult.output.definitionTheorem.sequent.concl ≠
      afterTwoTypesResult.output.definitionTheorem.sequent.concl := by
  decide +kernel

theorem type_instantiated_row_acceptance :
    ∃ certificate, (checker originalMixed).check (FirstOrder.renderSequent
      ⟨boolInstance.applyHypotheses afterTwoTypesResult.output.definitionTheorem.sequent.hyp,
        boolInstance.apply afterTwoTypesResult.output.definitionTheorem.sequent.concl⟩) certificate = true :=
  accepted_substitution originalMixed boolInstance late_original_row_acceptance

theorem configured_mixed_falsity_refused (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (certificate : SavedCertificate) :
    (checker secondByConfigured).check (FirstOrder.renderSequent ⟨∅, falsity⟩) certificate = false :=
  falsity_refused secondByConfigured primitives other assignment certificate

end Controls

end Mettapedia.Languages.HOLLight.UniversalDefinitionMeaning
