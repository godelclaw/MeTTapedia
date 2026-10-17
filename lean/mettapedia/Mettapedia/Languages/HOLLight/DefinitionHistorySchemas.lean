import Mettapedia.Languages.HOLLight.DefinitionSchemaSubstitution

/-!
# Universal source schemas across original mixed definition histories

The original chronological rows contribute their universal definition
schemas. Admission earns source formation and substitution support; later
installations preserve the original universal bodies through actual source
model agreement. The final constructed model then validates all images.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.DefinitionHistorySchemas

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionHistory MixedDefinitionModelFamily
open SourceTypeDefinitionTransport UniformTypeDefinitionModels
open DefinitionSchemaClosure DefinitionSchemaInstances DefinitionSchemaSubstitution

universe w

/-- A source-language witness for the universal formula. This contains
original syntax and formation licences, not a semantic truth assumption. -/
def LicensedSchema (signature : Signature) (formula : HOL.ClosedFormula Symbol) : Prop :=
  ∃ (context : HOL.Ctx AtomicTy) (source : DBTerm) (body : HOL.Formula Symbol context),
    TranslatesCompositionally context source .prop body ∧
    AnnotationsFormed signature source ∧ ContextFormed signature (context.map Ty.fromHOL) ∧
    formula = HOL.closeAll context body

theorem LicensedSchema.mono {source target : Signature} (included : source.Includes target)
    {formula : HOL.ClosedFormula Symbol} (licensed : LicensedSchema source formula) :
    LicensedSchema target formula := by
  obtain ⟨context, term, body, translation, formed, contextFormed, shape⟩ := licensed
  exact ⟨context, term, body, translation, formed.mono included,
    fun type member => (contextFormed type member).mono included, shape⟩

/-- Constant admission changes no old licensed carrier or symbol value. -/
theorem constant_old_agreement {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    SourceAgreement context.signature (ConstantAdmission.sourceExtension result M) M where
  carriers := fun _ _ => rfl
  constants := by
    intro constant annotation type typed _ declared
    obtain ⟨schema, substitution, registered, _⟩ := declared
    have different : constant ≠ result.output.constant := by
      intro same
      rw [same, ConstantAdmission.admitted_identity_fresh accepted] at registered
      cases registered
    exact heq_of_eq (ConstantAdmission.sourceExtension_constant_other result M constant annotation typed different)
  variableValues := fun sourceVar _ typed _ =>
    heq_of_eq (ConstantHistoryInstanceCoherence.sourceExtension_variable result M sourceVar typed)

theorem LicensedSchema.models_agreement {signature : Signature}
    {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (agreement : SourceAgreement signature first second)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    (firstFull : first.FullDomains) (secondFull : second.FullDomains)
    {formula : HOL.ClosedFormula Symbol} (licensed : LicensedSchema signature formula) :
    first.models formula ↔ second.models formula := by
  obtain ⟨context, term, body, translation, formed, contextFormed, rfl⟩ := licensed
  exact DefinitionSchemaInstances.SourceAgreement.models_closeAll agreement functionArity firstFull secondFull translation formed contextFormed

section Constant

variable {context : TheoryContext} {instances : InstanceWitnesses} {name : Name}
  {source : SourceTerm} {result : ContextConstantDefinitionResult}
  (accepted : admitConstantInTheory context instances name source = some result)

/-- The actual primitive-equality translation of the returned source row. -/
noncomputable def constantSchema (result : ContextConstantDefinitionResult) : HOL.ClosedFormula Symbol :=
  .app (.app (equalityLambda result.definition.ty.toHOL)
    (.const (.constant result.output.constant result.definition.ty rfl))) (ConstantAdmission.body result)

include accepted

private theorem constant_not_equality : result.output.constant ≠ Const.equality := by
  rw [(ConstantAdmission.source_equation accepted).1]
  intro same
  cases (Const.mk.inj same).2

theorem constantSchema_translated : TranslatesCompositionally []
    result.output.definitionTheorem.sequent.concl.term .prop (constantSchema result) := by
  rw [(ConstantAdmission.source_equation accepted).2.2]
  apply TranslatesCompositionally.equalityDB rfl
  · exact .constant (by simp [equalityOperand?, Const.same_eq_true_iff, constant_not_equality accepted]) rfl
  · exact ConstantAdmission.body_translated result

theorem constantSchema_ordinary (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    OrdinarySymbols (constantSchema result) := by
  have admitted := admitConstantInTheory_result accepted
  obtain ⟨definition, equality, checked, closed, _, _, _, _⟩ :=
    checkConstantDefinition_result admitted.2.2.2.2.1
  have sourceChecked := (checkSource_sound _ _ admitted.1).1
  have same := Option.some.inj (checked.symm.trans sourceChecked)
  have bodyClosed : result.definition.term.HasNoFreeVariables := same ▸ closed
  have ordinaryBody := ordinary_of_closed_translation context.signature parameter registered
    (ConstantAdmission.body_translated result) (checkSource_sound _ _ admitted.1).2 bodyClosed
  exact .app (.app (.lam (.lam (.eq (.var _) (.var _))))
    (.constant _ _ _ (constant_not_equality accepted))) ordinaryBody

theorem constantSchema_licensed (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    LicensedSchema result.context.signature (constantSchema result) :=
  ⟨[], result.output.definitionTheorem.sequent.concl.term, constantSchema result,
    constantSchema_translated accepted, constant_equation_formed accepted functionArity parameter registered,
    ContextFormed.nil _, rfl⟩

end Constant

section TypeSchemas

variable {context : TheoryContext} {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest}
  {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (functionArity : context.signature.typeOperators TypeOp.function = some 2)
  (parameter : Name)
  (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))

include accepted functionArity parameter registered

theorem abstractionSchema_licensed : LicensedSchema result.context.signature
    (abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty) := by
  have formed := DefinitionSchemaInstances.AnnotationsFormed.closeFreeAt
    (type_equations_formed accepted functionArity parameter registered).1
    ⟨Name.global "a", sourceCarrierType request TypeSubst.empty⟩ 0
  have annotation := result.context.constantTypes _ _ (UniformTypeDefinitionInstances.new_constants_registered accepted).1
  have carrier : TypeFormed result.context.signature (sourceCarrierType request TypeSubst.empty) := by
    simpa only [abstractionAnnotation, TypeSubst.apply_empty] using (annotation.function_components _).2
  refine ⟨[(sourceCarrierType request TypeSubst.empty).toHOL], _, _,
    abstractionRepresentation_body_translated accepted TypeSubst.empty, ?_, ?_, rfl⟩
  · simpa only [TermSubst.typeInstance_identity] using formed
  · simp only [List.map_cons, List.map_nil, Ty.fromHOL_toHOL]
    exact ContextFormed.cons _ carrier (ContextFormed.nil _)

theorem representationSchema_licensed : LicensedSchema result.context.signature
    (representationAbstractionSchema accepted TypeSubst.empty) := by
  have formed := DefinitionSchemaInstances.AnnotationsFormed.closeFreeAt
    (type_equations_formed accepted functionArity parameter registered).2
    ⟨Name.global "r", (instanceTerm TypeSubst.empty result.core.witness).ty⟩ 0
  refine ⟨[(instanceTerm TypeSubst.empty result.core.witness).ty.toHOL], _, _,
    representationAbstraction_body_translated accepted TypeSubst.empty, ?_, ?_, rfl⟩
  · simpa only [TermSubst.typeInstance_identity] using formed
  · simp only [List.map_cons, List.map_nil, Ty.fromHOL_toHOL]
    apply ContextFormed.cons
    · simpa only [instanceTerm, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked,
        TypeSubst.apply_empty] using
        (admitted_represented_formed accepted).mono (admitSourceTypeInTheory_result accepted).1
    · exact ContextFormed.nil _

end TypeSchemas

namespace History

/-- Ordered universal schemas of exactly the original chronological rows. -/
noncomputable def schemas {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) : List (HOL.ClosedFormula Symbol) := by
  induction history with
  | nil => exact []
  | constant prior instances name source result accepted ih => exact ih ++ [constantSchema result]
  | typeDefinition prior instances request result accepted existence ih =>
      exact ih ++ [abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty,
        representationAbstractionSchema accepted TypeSubst.empty]

theorem schemas_licensed {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) (primitives : Primitives initial)
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ schemas history) :
    LicensedSchema final.signature formula := by
  induction history with
  | nil => simp [schemas] at member
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

theorem schemas_ordinary {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) (primitives : Primitives initial)
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ schemas history) : OrdinarySymbols formula := by
  induction history with
  | nil => simp [schemas] at member
  | constant prior instances name source result accepted ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact ih earlier
      · obtain rfl := List.mem_singleton.mp added
        exact constantSchema_ordinary accepted primitives.equalityParameter
          (prior.includes.2 _ _ primitives.equalityRegistered)
  | typeDefinition prior instances request result accepted existence ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact ih earlier
      · rcases List.mem_cons.mp added with rfl | added
        · exact ordinary_abstractionSchema accepted
        · obtain rfl := List.mem_singleton.mp added
          exact ordinary_representationSchema accepted primitives.equalityParameter
            (prior.includes.2 _ _ primitives.equalityRegistered)


/-- The actual recurrence preserves earlier all-value schemas at every
later original installation, including carrier-changing type steps. -/
theorem schemas_models {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) (primitives : Primitives initial)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ schemas history) :
    (MixedDefinitionModels.model primitives history other assignment).models formula := by
  induction history generalizing other assignment with
  | nil => simp [schemas] at member
  | constant prior instances name source result accepted ih =>
      change (ConstantAdmission.sourceExtension result
        ((Construction.build primitives prior).model other assignment)).models formula
      rcases List.mem_append.mp member with earlier | added
      · apply (LicensedSchema.models_agreement
          (constant_old_agreement accepted ((Construction.build primitives prior).model other assignment))
          (prior.includes.1 _ _ primitives.functionArity)
          (ConstantAdmission.sourceExtension_fullDomains _ _
            ((Construction.build primitives prior).fullDomains other assignment))
          ((Construction.build primitives prior).fullDomains other assignment)
          (schemas_licensed prior primitives earlier)).mpr
        exact ih other assignment earlier
      · obtain rfl := List.mem_singleton.mp added
        exact ConstantAdmission.sourceExtension_models_source_equation accepted _ TypeSubst.empty
          ((constantSchema_translated accepted).of_term_eq (TermSubst.typeInstance_identity _).symm)
  | typeDefinition prior instances request result accepted existence ih =>
      change (MixedTypeDefinitionModels.model (Construction.build primitives prior) accepted existence other assignment).models formula
      rcases List.mem_append.mp member with earlier | added
      · apply (LicensedSchema.models_agreement
          (MixedTypeDefinitionModels.model_old_agreement (Construction.build primitives prior) accepted existence other assignment)
          (prior.includes.1 _ _ primitives.functionArity)
          (MixedTypeDefinitionModels.model_fullDomains (Construction.build primitives prior) accepted existence other assignment)
          ((Construction.build primitives prior).fullDomains other assignment)
          (schemas_licensed prior primitives earlier)).mpr
        exact ih other assignment earlier
      · rcases List.mem_cons.mp added with rfl | added
        · exact models_abstractionRepresentation (Construction.build primitives prior) accepted existence other assignment TypeSubst.empty
        · obtain rfl := List.mem_singleton.mp added
          apply models_representationAbstraction (Construction.build primitives prior) accepted existence other assignment primitives TypeSubst.empty
          have annotation := result.context.constantTypes _ _ (UniformTypeDefinitionInstances.new_constants_registered accepted).1
          simpa only [abstractionAnnotation, TypeSubst.apply_empty] using (annotation.function_components _).2

/-- The background is constructed from the original ordered universal
schemas and their actual finite type-image orbits. -/
noncomputable def background {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) : HOL.ClosedTheorySet Symbol :=
  {formula | ∃ schema ∈ schemas history, TypeImageOrbit schema formula}

theorem background_closed {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) (primitives : Primitives initial) :
    VariableFreeSubstitutionClosed (background history) where
  variableFree := by
    rintro formula ⟨schema, member, image⟩ sourceVar
    exact (image.ordinary (schemas_ordinary history primitives member)).variableFree sourceVar
  substitutionClosed := by
    rintro substitution formula ⟨schema, member, image⟩
    rw [targetMap_eq_typeMap (image.ordinary (schemas_ordinary history primitives member))]
    exact ⟨schema, member, TypeImageOrbit.image substitution.raw.types image⟩

/-- Final instance coherence is earned by the original mixed construction.
It gives truthful reducts of each retained universal schema, after which
actual model-reduct composition validates every iterated background image. -/
theorem background_models {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) (primitives : Primitives initial)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∀ formula ∈ background history, (MixedDefinitionModels.model primitives history other assignment).models formula := by
  let construction := Construction.build primitives history
  let M := construction.model other assignment
  have full := construction.fullDomains other assignment
  rintro formula ⟨schema, member, image⟩
  apply schemaTheory_models M full _ formula image
  intro substitution
  obtain ⟨context, term, body, translation, formed, contextFormed, shape⟩ := schemas_licensed history primitives member
  rw [shape]
  apply (reindexedModel_models substitution M full _).mpr
  apply (models_closeAll_instance construction primitives other assignment substitution translation formed contextFormed).mp
  rw [← shape]
  exact schemas_models history primitives other _ member


/-- Universal schema order and physical declaration-row multiplicity agree. -/
theorem schemas_length {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) : (schemas history).length = records.length := by
  induction history with
  | nil => rfl
  | constant prior instances name source result accepted ih =>
      change (schemas prior ++ [_]).length = _
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [ih]
  | typeDefinition prior instances request result accepted existence ih =>
      change (schemas prior ++ [_, _]).length = _
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [ih]

/-- Preserving the authored schema prefix preserves its actual image theory. -/
theorem background_mono {initial first last : TheoryContext} {firstRows lastRows : List Theorem}
    {firstHistory : History initial first firstRows} {lastHistory : History initial last lastRows}
    (subset : schemas firstHistory ⊆ schemas lastHistory) : background firstHistory ⊆ background lastHistory := by
  rintro formula ⟨schema, member, image⟩
  exact ⟨schema, subset member, image⟩

private theorem translated_mono {first second : HOL.ClosedTheorySet Symbol}
    (subset : first ⊆ second) {sequent : Sequent} (proof : TranslatedProvable first sequent) :
    TranslatedProvable second sequent := by
  obtain ⟨formula, translation, derivation⟩ := proof
  exact ⟨formula, translation, HOL.ClosedTheorySet.provable_mono
    (fun member => member.elim (fun earlier => Or.inl (subset earlier)) Or.inr) derivation⟩

/-- Each actual retained finite row is proved from the universal background.
Earlier rows retain their exact identity; pointwise type rows are obtained by
universal elimination rather than treated as free-variable background axioms. -/
theorem record_translated_provable {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) {recorded : Theorem} (member : recorded ∈ records) :
    TranslatedProvable (background history) recorded.sequent := by
  induction history with
  | nil => simp at member
  | constant prior instances name source result accepted ih =>
      rcases List.mem_append.mp member with earlier | added
      · apply translated_mono _ (ih earlier)
        exact background_mono (fun _ included => List.mem_append_left _ included)
      · obtain rfl := List.mem_singleton.mp added
        apply (translatedProvable_iff_compositionallyProvable _ _).mpr
        refine ⟨constantSchema result, constantSchema_translated accepted, ?_⟩
        apply HOL.ClosedTheorySet.provable_of_mem
        exact Or.inl ⟨constantSchema result, List.mem_append_right _ (List.mem_cons_self), TypeImageOrbit.original⟩
  | typeDefinition prior instances request result accepted existence ih =>
      rcases List.mem_append.mp member with earlier | added
      · apply translated_mono _ (ih earlier)
        exact background_mono (fun _ included => List.mem_append_left _ included)
      · have localSubset : typeDefinitionTheory accepted ⊆
          background (History.typeDefinition prior instances request result accepted existence) := by
          rintro formula (first | second)
          · exact ⟨_, List.mem_append_right _ List.mem_cons_self, first⟩
          · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), second⟩
        rcases List.mem_cons.mp added with rfl | added
        · exact translated_mono localSubset (definition_rows_translated_provable accepted _ List.mem_cons_self)
        · obtain rfl := List.mem_singleton.mp added
          exact translated_mono localSubset (definition_rows_translated_provable accepted _
            (List.mem_cons_of_mem _ List.mem_cons_self))

/-- Actual configured kernel proofs are interpreted against the earned
whole-history universal background. This does not reclassify the weaker
pointwise equationTheory as closed under unrestricted source INST. -/
theorem configured_kernel_provable {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) (primitives : Primitives initial)
    (policy : AxiomPolicy)
    (authorizedRows : ∀ sequent, policy sequent → ∃ recorded ∈ records, recorded.sequent = sequent)
    {out : Theorem} (derived : Mettapedia.Logic.Derives (HOLLight.Rule policy) out) :
    TranslatedProvable (background history) out.sequent := by
  apply derives_translatedProvable_of_policy (background_closed history primitives) _ (derives_shared policy derived)
  intro sequent authorized
  obtain ⟨recorded, member, rfl⟩ := authorizedRows sequent authorized
  exact record_translated_provable history member

/-- A configured original existence proof earns a syntactic proof over the
real preceding universal background. Admission discharges its empty-hypothesis
guard; no model-truth or whole-history proof is supplied as a hypothesis. -/
theorem configured_existence_provable {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) (primitives : Primitives initial)
    (policy : AxiomPolicy)
    (authorizedRows : ∀ sequent, policy sequent → ∃ recorded ∈ records, recorded.sequent = sequent)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory final instances request = some result)
    (derived : Mettapedia.Logic.Derives (HOLLight.Rule policy) request.existence) :
    HOL.ClosedTheorySet.Provable (background history) (TypeAdmission.admittedImage accepted).formula := by
  have provable := (translatedProvable_iff_compositionallyProvable _ _).mp
    (configured_kernel_provable history primitives policy authorizedRows derived)
  obtain ⟨formula, translated, proven⟩ := provable
  have same := eq_of_heq (translated.unique (TypeAdmission.admittedImage accepted).conclusionTranslated).2
  subst formula
  apply HOL.ClosedTheorySet.provable_mono _ proven
  rintro sentence (backgroundMember | hypotheses)
  · exact backgroundMember
  · obtain ⟨term, member, _⟩ := hypotheses
    rw [(UniformTypeDefinitionFamily.admitted_parameter_guards accepted).2.2] at member
    exact absurd member (Finset.notMem_empty _)

/-- The entire universally bound history background has the constructed
model, so its syntactic proof theory refuses falsity. -/
theorem background_consistent {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) (primitives : Primitives initial)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    HOL.ClosedTheorySet.Consistent (background history) := by
  intro contradiction
  exact provable_models contradiction (MixedDefinitionModels.model primitives history other assignment)
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _ (MixedDefinitionModels.fullDomains primitives history other assignment))
    (background_models history primitives other assignment)

end History


namespace Controls

open MixedDefinitionHistory.Controls MixedDefinitionModelFamily.Controls
open MixedDefinitionModels.Controls

theorem original_mixed_schema_count : (History.schemas afterTwoTypesHistory).length = 8 := by
  rw [History.schemas_length]
  rfl

theorem whole_mixed_background_closed : VariableFreeSubstitutionClosed (History.background afterTwoTypesHistory) :=
  History.background_closed afterTwoTypesHistory primitives

theorem whole_mixed_background_models (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∀ formula ∈ History.background afterTwoTypesHistory,
      (MixedDefinitionModels.model primitives afterTwoTypesHistory other assignment).models formula :=
  History.background_models afterTwoTypesHistory primitives other assignment

theorem last_original_row_provable : TranslatedProvable (History.background afterTwoTypesHistory)
    afterTwoTypesResult.output.definitionTheorem.sequent :=
  History.record_translated_provable afterTwoTypesHistory (List.mem_append_right _ List.mem_cons_self)

/-- The concrete policy authorizes a genuine retained source row. -/
def lastRowPolicy : AxiomPolicy := fun sequent => sequent = afterTwoTypesResult.output.definitionTheorem.sequent

private theorem lastRow_hyp_empty : afterTwoTypesResult.output.definitionTheorem.sequent.hyp = ∅ :=
  (admitConstantInTheory_result after_two_types_result_admitted).2.2.2.2.2.2.2

private theorem lastRow_bool : afterTwoTypesResult.output.definitionTheorem.sequent.IsBool := by
  constructor
  · exact (ConstantAdmission.source_equation after_two_types_result_admitted).2.resultIsBool
  · intro term member
    rw [lastRow_hyp_empty] at member
    exact absurd member (Finset.notMem_empty _)

noncomputable def lastRowAxiom : Theorem :=
  Theorem.axiomResult afterTwoTypesResult.output.definitionTheorem.sequent lastRow_bool

theorem lastRow_derived : Mettapedia.Logic.Derives (HOLLight.Rule lastRowPolicy) lastRowAxiom := by
  refine Mettapedia.Logic.Derives.node [] lastRowAxiom ?_ ?_
  · exact Or.inr ⟨_, rfl, lastRow_hyp_empty, rfl, lastRow_bool, rfl, rfl, rfl⟩
  · intro premise member; cases member

/-- An actual nonempty configured kernel derivation consumes the earned
whole-history background through the original policy/kernel authority. -/
theorem configured_last_row_provable :
    TranslatedProvable (History.background afterTwoTypesHistory) lastRowAxiom.sequent := by
  apply History.configured_kernel_provable afterTwoTypesHistory primitives lastRowPolicy _ lastRow_derived
  intro sequent authorized
  exact ⟨afterTwoTypesResult.output.definitionTheorem, List.mem_append_right _ List.mem_cons_self, authorized.symm⟩

theorem configured_second_existence : HOL.ClosedTheorySet.Provable (History.background afterTypeHistory)
    (TypeAdmission.admittedImage second_result_admitted).formula :=
  History.configured_existence_provable afterTypeHistory primitives emptyAxiomPolicy
    (fun _ impossible => False.elim impossible) second_result_admitted second_existence_derived

/-- Even the final background never admits the unbound original value row
as a member: its role remains a proved universal instance. -/
theorem unbound_second_row_not_background :
    abstractionRepresentationFormula (request := secondRequest) (result := secondResult) TypeSubst.empty ∉
      History.background afterTwoTypesHistory := by
  intro member
  exact original_abstractionRepresentation_has_free_value TypeSubst.empty
    (whole_mixed_background_closed.variableFree _ member _)

theorem whole_mixed_refuses_falsity (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ¬ HOL.ClosedTheorySet.Provable (History.background afterTwoTypesHistory) (.bot : HOL.ClosedFormula Symbol) :=
  History.background_consistent afterTwoTypesHistory primitives other assignment

end Controls

end Mettapedia.Languages.HOLLight.DefinitionHistorySchemas
