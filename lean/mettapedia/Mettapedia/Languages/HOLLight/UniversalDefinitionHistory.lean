import Mettapedia.Languages.HOLLight.DefinitionHistoryMeaning

/-!
# Universal-predecessor chronology of original HOL declarations

Type steps consume syntactic proofs over the genuinely universally closed
preceding definition schemas. The exact original source admission, theorem
rows and occurrence order are retained. The older pointwise-predecessor
history embeds by a proved syntactic transfer, without changing its receipts.

This is a declaration chronology, not a replacement source proof checker.
Model construction for the generalized chronology is a subsequent join.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.UniversalDefinitionHistory

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionModelFamily
open SourceTypeDefinitionTransport UniformTypeDefinitionModels
open DefinitionSchemaClosure DefinitionSchemaInstances DefinitionSchemaSubstitution

/-- The actual image theory of the ordered original universal schemas. -/
def schemaBackground (schemas : List (HOL.ClosedFormula Symbol)) : HOL.ClosedTheorySet Symbol :=
  {formula | ∃ schema ∈ schemas, TypeImageOrbit schema formula}

/-- Exact original admissions, with their syntactic existence licence drawn
from the real preceding universal theory. No interpretation or final semantic
coherence is supplied to this chronological source carrier. -/
inductive History (initial : TheoryContext) : TheoryContext → List Theorem →
    List (HOL.ClosedFormula Symbol) → Type where
  | nil : History initial initial [] []
  | constant {before : TheoryContext} {records : List Theorem} {schemas : List (HOL.ClosedFormula Symbol)}
      (prior : History initial before records schemas)
      (instances : InstanceWitnesses) (name : Name) (source : SourceTerm)
      (result : ContextConstantDefinitionResult)
      (accepted : admitConstantInTheory before instances name source = some result) :
      History initial result.context (records ++ [result.output.definitionTheorem])
        (schemas ++ [DefinitionHistorySchemas.constantSchema result])
  | typeDefinition {before : TheoryContext} {records : List Theorem} {schemas : List (HOL.ClosedFormula Symbol)}
      (prior : History initial before records schemas)
      (instances : InstanceWitnesses) (request : TypeOperatorDefinitionRequest)
      (result : SourceTypeDefinitionResult)
      (accepted : admitSourceTypeInTheory before instances request = some result)
      (existence : HOL.ClosedTheorySet.Provable (schemaBackground schemas)
        (TypeAdmission.admittedImage accepted).formula) :
      History initial result.context
        (records ++ [result.output.abstractionRepresentationTheorem, result.output.representationAbstractionTheorem])
        (schemas ++ [abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty,
          representationAbstractionSchema accepted TypeSubst.empty])

/-- Every pointwise source type instance in the older theory is genuinely
proved in its earned universal background. The actual original substitution
operation, rather than semantic truth, earns the transfer. -/
theorem restricted_equation_provable {initial final : TheoryContext} {records : List Theorem}
    (history : MixedDefinitionHistory.History initial final records) (primitives : Primitives initial)
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ MixedDefinitionHistory.equationTheory records) :
    HOL.ClosedTheorySet.Provable (schemaBackground (DefinitionHistorySchemas.History.schemas history)) formula := by
  obtain ⟨recorded, present, substitution, translated⟩ := member
  have original := (translatedProvable_iff_compositionallyProvable _ _).mp
    (DefinitionHistorySchemas.History.record_translated_provable history present)
  have instantiated := compositionallyProvable_subst
    (DefinitionHistorySchemas.History.background_closed history primitives)
    (TypeCorrectTermSubstitution.ofTypes substitution) original
  obtain ⟨actual, actualTranslation, proven⟩ := instantiated
  have same : actual = formula := eq_of_heq (actualTranslation.unique translated).2
  subst actual
  apply HOL.ClosedTheorySet.provable_mono _ proven
  rintro sentence (backgroundMember | hypotheses)
  · exact backgroundMember
  · obtain ⟨term, presentHypothesis, _⟩ := hypotheses
    have empty := (DefinitionHistoryMeaning.record_metadata history present).1
    simp only [TypeCorrectTermSubstitution.applyHypotheses, empty, Finset.image_empty] at presentHypothesis
    exact absurd presentHypothesis (Finset.notMem_empty _)

namespace History

/-- Restricted original histories embed with exactly the same admissions,
row vector and universal-schema vector. Their preceding proofs transfer by
syntactic derivation; unrestricted INST closure is not assigned to the old
pointwise theory itself. -/
noncomputable def ofRestricted {initial final : TheoryContext} {records : List Theorem}
    (primitives : Primitives initial) (history : MixedDefinitionHistory.History initial final records) :
    History initial final records (DefinitionHistorySchemas.History.schemas history) := by
  induction history with
  | nil => exact .nil
  | constant prior instances name source result accepted ih => exact .constant ih instances name source result accepted
  | typeDefinition prior instances request result accepted existence ih =>
      apply History.typeDefinition ih instances request result accepted
      apply provable_of_forall_provable existence
      intro formula member
      exact restricted_equation_provable prior primitives member

variable {initial final : TheoryContext} {records : List Theorem} {schemas : List (HOL.ClosedFormula Symbol)}

theorem includes (history : History initial final records schemas) :
    initial.signature.Includes final.signature := by
  induction history with
  | nil => exact Signature.Includes.refl _
  | constant prior instances name source result accepted ih =>
      exact ih.trans (admitConstantInTheory_result accepted).2.2.1
  | typeDefinition prior instances request result accepted existence ih =>
      exact ih.trans (admitSourceTypeInTheory_result accepted).1

theorem schemas_ordinary (history : History initial final records schemas) (primitives : Primitives initial)
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ schemas) : OrdinarySymbols formula := by
  induction history with
  | nil => simp at member
  | constant prior instances name source result accepted ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact ih earlier
      · obtain rfl := List.mem_singleton.mp added
        exact DefinitionHistorySchemas.constantSchema_ordinary accepted primitives.equalityParameter
          (prior.includes.2 _ _ primitives.equalityRegistered)
  | typeDefinition prior instances request result accepted existence ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact ih earlier
      · rcases List.mem_cons.mp added with rfl | added
        · exact ordinary_abstractionSchema accepted
        · obtain rfl := List.mem_singleton.mp added
          exact ordinary_representationSchema accepted primitives.equalityParameter
            (prior.includes.2 _ _ primitives.equalityRegistered)

theorem background_closed (history : History initial final records schemas) (primitives : Primitives initial) :
    VariableFreeSubstitutionClosed (schemaBackground schemas) where
  variableFree := by
    rintro formula ⟨schema, member, image⟩ sourceVar
    exact (image.ordinary (history.schemas_ordinary primitives member)).variableFree sourceVar
  substitutionClosed := by
    rintro substitution formula ⟨schema, member, image⟩
    rw [targetMap_eq_typeMap (image.ordinary (history.schemas_ordinary primitives member))]
    exact ⟨schema, member, TypeImageOrbit.image substitution.raw.types image⟩

private theorem background_prefix (first second : List (HOL.ClosedFormula Symbol)) :
    schemaBackground first ⊆ schemaBackground (first ++ second) := by
  rintro formula ⟨schema, member, image⟩
  exact ⟨schema, List.mem_append_left _ member, image⟩

private theorem translated_mono {first second : HOL.ClosedTheorySet Symbol} (included : first ⊆ second)
    {sequent : Sequent} (proof : TranslatedProvable first sequent) : TranslatedProvable second sequent := by
  obtain ⟨formula, translated, derivation⟩ := proof
  exact ⟨formula, translated, HOL.ClosedTheorySet.provable_mono
    (fun member => member.elim (fun member => Or.inl (included member)) Or.inr) derivation⟩

/-- Original finite definition rows are syntactically proved from the
actual universal predecessor theory at every generalized source step. -/
theorem record_translated_provable (history : History initial final records schemas)
    {recorded : Theorem} (member : recorded ∈ records) :
    TranslatedProvable (schemaBackground schemas) recorded.sequent := by
  induction history with
  | nil => simp at member
  | constant prior instances name source result accepted ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact translated_mono (background_prefix _ _) (ih earlier)
      · obtain rfl := List.mem_singleton.mp added
        apply (translatedProvable_iff_compositionallyProvable _ _).mpr
        refine ⟨DefinitionHistorySchemas.constantSchema result, DefinitionHistorySchemas.constantSchema_translated accepted, ?_⟩
        apply HOL.ClosedTheorySet.provable_of_mem
        exact Or.inl ⟨_, List.mem_append_right _ List.mem_cons_self, TypeImageOrbit.original⟩
  | @typeDefinition before oldRows priorSchemas prior instances request result accepted existence ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact translated_mono (background_prefix _ _) (ih earlier)
      · have localSubset : typeDefinitionTheory accepted ⊆ schemaBackground
          (priorSchemas ++ [abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty,
            representationAbstractionSchema accepted TypeSubst.empty]) := by
          rintro formula (first | second)
          · exact ⟨_, List.mem_append_right _ List.mem_cons_self, first⟩
          · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), second⟩
        rcases List.mem_cons.mp added with rfl | added
        · exact translated_mono localSubset (definition_rows_translated_provable accepted _ List.mem_cons_self)
        · obtain rfl := List.mem_singleton.mp added
          exact translated_mono localSubset (definition_rows_translated_provable accepted _
            (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The actual configured source kernel supplies syntactic derivability in
the generalized chronology's earned universal background. -/
theorem configured_kernel_provable (history : History initial final records schemas) (primitives : Primitives initial)
    (policy : AxiomPolicy)
    (authorizedRows : ∀ sequent, policy sequent → ∃ recorded ∈ records, recorded.sequent = sequent)
    {out : Theorem} (derived : Mettapedia.Logic.Derives (HOLLight.Rule policy) out) :
    TranslatedProvable (schemaBackground schemas) out.sequent := by
  apply derives_translatedProvable_of_policy (history.background_closed primitives) _ (derives_shared policy derived)
  intro sequent authorized
  obtain ⟨recorded, member, rfl⟩ := authorizedRows sequent authorized
  exact history.record_translated_provable member

/-- Original source admission plus an actual preceding configured derivation
computes the stronger chronological type-step licence. No bare-kernel-only
restriction or supplied semantic existence conclusion is imposed. -/
noncomputable def typeOfConfigured (history : History initial final records schemas) (primitives : Primitives initial)
    (policy : AxiomPolicy)
    (authorizedRows : ∀ sequent, policy sequent → ∃ recorded ∈ records, recorded.sequent = sequent)
    (instances : InstanceWitnesses) (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory final instances request = some result)
    (derived : Mettapedia.Logic.Derives (HOLLight.Rule policy) request.existence) :
    History initial result.context
      (records ++ [result.output.abstractionRepresentationTheorem, result.output.representationAbstractionTheorem])
      (schemas ++ [abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty,
        representationAbstractionSchema accepted TypeSubst.empty]) := by
  apply History.typeDefinition history instances request result accepted
  have proof := (translatedProvable_iff_compositionallyProvable _ _).mp
    (history.configured_kernel_provable primitives policy authorizedRows derived)
  obtain ⟨formula, translated, proven⟩ := proof
  have same := eq_of_heq (translated.unique (TypeAdmission.admittedImage accepted).conclusionTranslated).2
  subst formula
  apply HOL.ClosedTheorySet.provable_mono _ proven
  rintro sentence (backgroundMember | hypotheses)
  · exact backgroundMember
  · obtain ⟨term, member, _⟩ := hypotheses
    rw [(UniformTypeDefinitionFamily.admitted_parameter_guards accepted).2.2] at member
    exact absurd member (Finset.notMem_empty _)

/-- The generalized carrier adds exactly one schema per original row,
including duplicated row occurrences; it cannot skip a declaration slot. -/
theorem schemas_length (history : History initial final records schemas) : schemas.length = records.length := by
  induction history with
  | nil => rfl
  | constant prior instances name source result accepted ih =>
      simp only [List.length_append, List.length_cons, List.length_nil, ih]
  | typeDefinition prior instances request result accepted existence ih =>
      simp only [List.length_append, List.length_cons, List.length_nil, ih]

end History

namespace Controls

open MixedDefinitionHistory.Controls MixedDefinitionModelFamily.Controls
open MixedDefinitionModels.Controls UniformTypeDefinitionFamily.Controls

/-- This is the same eight original rows, with the predecessor-theory
licence strengthened by the proved restricted-history embedding. -/
noncomputable def originalMixed : History DefinitionAdapters.ContextControls.coreContext afterTwoTypesResult.context
    ((((DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
      (fun result => result.output.definitionTheorem) ++
      [polymorphicResult.output.abstractionRepresentationTheorem,
       polymorphicResult.output.representationAbstractionTheorem]) ++
      [afterTypeResult.output.definitionTheorem]) ++
      [secondResult.output.abstractionRepresentationTheorem, secondResult.output.representationAbstractionTheorem]) ++
      [afterTwoTypesResult.output.definitionTheorem])
    (DefinitionHistorySchemas.History.schemas afterTwoTypesHistory) :=
  History.ofRestricted primitives afterTwoTypesHistory

theorem original_mixed_background_closed :
    VariableFreeSubstitutionClosed (schemaBackground (DefinitionHistorySchemas.History.schemas afterTwoTypesHistory)) :=
  originalMixed.background_closed primitives

theorem original_mixed_last_row : TranslatedProvable
    (schemaBackground (DefinitionHistorySchemas.History.schemas afterTwoTypesHistory))
    afterTwoTypesResult.output.definitionTheorem.sequent :=
  originalMixed.record_translated_provable (List.mem_append_right _ List.mem_cons_self)

/-- Actual preceding kernel proof and original source admission create the
second type step through the unrestricted universal predecessor API. -/
noncomputable def secondByConfigured :=
  History.typeOfConfigured (History.ofRestricted primitives afterTypeHistory) primitives emptyAxiomPolicy
    (fun _ impossible => False.elim impossible) secondInstances secondRequest secondResult
    second_result_admitted second_existence_derived

theorem configured_second_background_closed :
    VariableFreeSubstitutionClosed (schemaBackground
      (DefinitionHistorySchemas.History.schemas afterTypeHistory ++
      [abstractionRepresentationSchema (request := secondRequest) (result := secondResult) TypeSubst.empty,
       representationAbstractionSchema second_result_admitted TypeSubst.empty])) :=
  secondByConfigured.background_closed primitives

theorem configured_second_row_provable : TranslatedProvable (schemaBackground
    (DefinitionHistorySchemas.History.schemas afterTypeHistory ++
    [abstractionRepresentationSchema (request := secondRequest) (result := secondResult) TypeSubst.empty,
     representationAbstractionSchema second_result_admitted TypeSubst.empty]))
    secondResult.output.abstractionRepresentationTheorem.sequent :=
  secondByConfigured.record_translated_provable (List.mem_append_right _ List.mem_cons_self)

/-- Exact predecessor rows, before the second type's own equations exist. -/
def beforeSecondRows : List Theorem :=
  (DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map (fun result => result.output.definitionTheorem) ++
    [polymorphicResult.output.abstractionRepresentationTheorem,
     polymorphicResult.output.representationAbstractionTheorem]) ++ [afterTypeResult.output.definitionTheorem]

/-- The future second row cannot satisfy the actual chronological authority
condition before its source declaration has been appended. -/
theorem future_second_row_not_authorized :
    ¬ ∃ recorded ∈ beforeSecondRows,
      recorded.sequent = secondResult.output.abstractionRepresentationTheorem.sequent := by
  decide +kernel

theorem repeated_original_admission_refused :
    admitSourceTypeInTheory polymorphicResult.context polymorphicCertificates polymorphicRequest = none :=
  MixedDefinitionHistory.Controls.repeated_type_refused

end Controls

end Mettapedia.Languages.HOLLight.UniversalDefinitionHistory
