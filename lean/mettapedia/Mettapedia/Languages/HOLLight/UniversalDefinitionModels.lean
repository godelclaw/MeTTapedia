import Mettapedia.Languages.HOLLight.UniversalDefinitionHistory
import Mettapedia.Languages.HOLLight.DefinitionModelInstallation

/-!
# Constructed models of universal-predecessor HOL histories

Every original constant/type admission constructs the next interpretation.
Type witnesses are interpreted from syntactic proofs over the actual
preceding universal background. The recurrence earns parameter support,
all-instance coherence, old source preservation and complete background
truth; no final model or existence truth is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.UniversalDefinitionModels

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters DefinitionModelFamily UniversalDefinitionHistory
open DefinitionSchemaClosure DefinitionSchemaInstances DefinitionSchemaSubstitution
open DefinitionHistorySchemas (LicensedSchema constantSchema constantSchema_translated
  constantSchema_licensed abstractionSchema_licensed representationSchema_licensed constant_old_agreement)
open SourceTypeDefinitionTransport UniformTypeDefinitionModels

universe w

/-- Original source formation licences survive the exact declaration chronology. -/
theorem schemas_licensed {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)} (history : History initial final records schemas)
    (primitives : Primitives initial) {formula : HOL.ClosedFormula Symbol} (member : formula ∈ schemas) :
    LicensedSchema final.signature formula := by
  induction history with
  | nil => simp at member
  | constant prior instances name source result accepted ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact (ih earlier).mono (admitConstantInTheory_result accepted).2.2.1
      · obtain rfl := List.mem_singleton.mp added
        exact constantSchema_licensed accepted (prior.includes.1 _ _ primitives.functionArity)
          primitives.equalityParameter (prior.includes.2 _ _ primitives.equalityRegistered)
  | typeDefinition prior instances request result accepted existence ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact (ih earlier).mono (admitSourceTypeInTheory_result accepted).1
      · rcases List.mem_cons.mp added with rfl | added
        · exact abstractionSchema_licensed accepted (prior.includes.1 _ _ primitives.functionArity)
            primitives.equalityParameter (prior.includes.2 _ _ primitives.equalityRegistered)
        · obtain rfl := List.mem_singleton.mp added
          exact representationSchema_licensed accepted (prior.includes.1 _ _ primitives.functionArity)
            primitives.equalityParameter (prior.includes.2 _ _ primitives.equalityRegistered)

/-- Earned model instance coherence validates the complete actual type-image
orbit of each licensed universal source schema. -/
theorem background_models_of_schemas {initial final : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}
    (family : Family.{w} initial final theory) (primitives : Primitives initial)
    (schemas : List (HOL.ClosedFormula Symbol))
    (licensed : ∀ formula ∈ schemas, LicensedSchema final.signature formula)
    (base : ∀ other assignment formula, formula ∈ schemas → (family.model other assignment).models formula)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∀ formula ∈ schemaBackground schemas, (family.model other assignment).models formula := by
  rintro formula ⟨schema, member, image⟩
  let M := family.model other assignment
  have full := family.fullDomains other assignment
  apply schemaTheory_models M full _ formula image
  intro substitution
  obtain ⟨context, term, body, translation, formed, contextFormed, shape⟩ := licensed schema member
  rw [shape]
  apply (reindexedModel_models substitution M full _).mpr
  apply (family_models_closeAll_instance family primitives other assignment substitution
    translation formed contextFormed).mp
  rw [← shape]
  exact base other _ schema member

/-- The actual chronology constructs one complete semantic family, including
truth of its preceding universal theory at every parameter assignment. -/
noncomputable def build {initial final : TheoryContext} {records : List Theorem}
    {schemas : List (HOL.ClosedFormula Symbol)} (primitives : Primitives initial)
    (history : History initial final records schemas) : Family.{w} initial final (schemaBackground schemas) := by
  induction history with
  | nil =>
      apply (Family.nil primitives).retheorize (schemaBackground [])
      rintro other assignment formula ⟨schema, member, image⟩
      simp at member
  | @constant before oldRows oldSchemas prior instances name source result accepted ih =>
      let core := Family.constantCore primitives ih instances name source result accepted
      apply core.retheorize (schemaBackground (oldSchemas ++ [constantSchema result]))
      intro outputOther outputAssignment
      apply background_models_of_schemas core primitives _ _ _ outputOther outputAssignment
      · intro formula member
        exact schemas_licensed (History.constant prior instances name source result accepted) primitives member
      · intro other assignment formula member
        rcases List.mem_append.mp member with earlier | added
        · apply (LicensedSchema.models_agreement
            (constant_old_agreement accepted (ih.model other assignment))
            (prior.includes.1 _ _ primitives.functionArity)
            (core.fullDomains other assignment) (ih.fullDomains other assignment)
            (schemas_licensed prior primitives earlier)).mpr
          exact ih.equations other assignment formula ⟨formula, earlier, TypeImageOrbit.original⟩
        · obtain rfl := List.mem_singleton.mp added
          exact ConstantAdmission.sourceExtension_models_source_equation accepted _ TypeSubst.empty
            ((constantSchema_translated accepted).of_term_eq (TermSubst.typeInstance_identity _).symm)
  | @typeDefinition before oldRows oldSchemas prior instances request result accepted existence ih =>
      let core := Family.typeDefinitionCore primitives ih instances request result accepted existence
      apply core.retheorize (schemaBackground (oldSchemas ++
        [abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty,
          representationAbstractionSchema accepted TypeSubst.empty]))
      intro outputOther outputAssignment
      apply background_models_of_schemas core primitives _ _ _ outputOther outputAssignment
      · intro formula member
        exact schemas_licensed (History.typeDefinition prior instances request result accepted existence) primitives member
      · intro other assignment formula member
        rcases List.mem_append.mp member with earlier | added
        · apply (LicensedSchema.models_agreement
            (TypeDefinitionModels.model_old_agreement ih accepted existence other assignment)
            (prior.includes.1 _ _ primitives.functionArity)
            (core.fullDomains other assignment) (ih.fullDomains other assignment)
            (schemas_licensed prior primitives earlier)).mpr
          exact ih.equations other assignment formula ⟨formula, earlier, TypeImageOrbit.original⟩
        · rcases List.mem_cons.mp added with rfl | added
          · exact family_models_abstractionRepresentation ih accepted existence other assignment TypeSubst.empty
          · obtain rfl := List.mem_singleton.mp added
            apply family_models_representationAbstraction ih accepted existence other assignment primitives TypeSubst.empty
            have annotation := result.context.constantTypes _ _ (UniformTypeDefinitionInstances.new_constants_registered accepted).1
            simpa only [abstractionAnnotation, TypeSubst.apply_empty] using (annotation.function_components _).2

variable {initial final : TheoryContext} {records : List Theorem}
  {schemas : List (HOL.ClosedFormula Symbol)} (primitives : Primitives initial)
  (history : History initial final records schemas) (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

noncomputable def model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  (build primitives history).model other assignment

theorem fullDomains : (model primitives history other assignment).FullDomains :=
  (build primitives history).fullDomains other assignment

theorem models_background : ∀ formula ∈ schemaBackground schemas,
    (model primitives history other assignment).models formula :=
  (build primitives history).equations other assignment

theorem models_provable {formula : HOL.ClosedFormula Symbol}
    (proof : HOL.ClosedTheorySet.Provable (schemaBackground schemas) formula) :
    (model primitives history other assignment).models formula :=
  provable_models proof _ (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _
    (fullDomains primitives history other assignment)) (models_background primitives history other assignment)

theorem symbol_local : ModelAssignmentSupport.SymbolLocal (model primitives history other) :=
  (build primitives history).localSymbols other

theorem source_instances (later : Signature)
    (types : ∀ operator arity, final.signature.typeOperators operator = some arity → later.typeOperators operator = some arity)
    (substitution : TypeSubst) :
    SourceAgreement (ConstantHistoryExpandedTypes.withTypes final.signature later)
      (model primitives history other
        (reindex (primitiveFamilies ((build primitives history).operators other)) substitution assignment))
      (reindexedModel substitution (model primitives history other assignment)) :=
  (build primitives history).instances other later types assignment substitution

/-- Formed original initial-language sentences retain their exact meaning
through all original constant and carrier-changing type steps. -/
theorem models_initial {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (formed : AnnotationsFormed initial.signature term)
    (translation : TranslatesCompositionally [] term .prop formula) :
    (model primitives history other assignment).models formula ↔ (initialModel other assignment).models formula := by
  induction history with
  | nil => exact Iff.rfl
  | constant prior instances name source result accepted ih =>
      exact (ConstantAdmission.sourceExtension_preserves_old_truth accepted
        ((build primitives prior).model other assignment) (formed.mono prior.includes) translation).trans ih
  | typeDefinition prior instances request result accepted existence ih =>
      exact (TypeDefinitionModels.model_models_old (build primitives prior) accepted existence
        other assignment primitives.functionArity translation (formed.mono prior.includes)).trans ih

include primitives history other assignment in
/-- The actual universal-predecessor theory is consistent in the constructed model. -/
theorem not_provable_falsity : ¬ HOL.ClosedTheorySet.Provable (schemaBackground schemas) (.bot : HOL.ClosedFormula Symbol) := by
  intro contradiction
  exact models_provable primitives history other assignment contradiction

namespace Controls

open UniversalDefinitionHistory.Controls
open MixedDefinitionModelFamily.Controls (primitives)

theorem original_interleaving_has_full_model (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (model MixedDefinitionModelFamily.Controls.primitives originalMixed other assignment).FullDomains := fullDomains _ _ _ _

theorem configured_second_has_true_background (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∀ formula ∈ schemaBackground (DefinitionHistorySchemas.History.schemas MixedDefinitionHistory.Controls.twoTypesHistory),
      (model MixedDefinitionModelFamily.Controls.primitives secondByConfigured other assignment).models formula :=
  models_background _ _ _ _

theorem configured_second_falsity_refused (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ¬ HOL.ClosedTheorySet.Provable
      (schemaBackground (DefinitionHistorySchemas.History.schemas MixedDefinitionHistory.Controls.twoTypesHistory))
      (.bot : HOL.ClosedFormula Symbol) :=
  not_provable_falsity MixedDefinitionModelFamily.Controls.primitives secondByConfigured other assignment

end Controls

end Mettapedia.Languages.HOLLight.UniversalDefinitionModels
