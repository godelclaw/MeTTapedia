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

/-- The admitted equation at an actual source type instance. -/
noncomputable def constantInstanceSchema (result : ContextConstantDefinitionResult)
    (substitution : TypeSubst) : HOL.ClosedFormula Symbol :=
  .app (.app (equalityLambda (substitution.apply result.definition.ty).toHOL)
    (.const (.constant result.output.constant (substitution.apply result.definition.ty) rfl)))
    (ConstantAdmission.instanceBody result substitution)

theorem constantInstanceSchema_translated {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (substitution : TypeSubst) : TranslatesCompositionally []
      ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
        result.output.definitionTheorem.sequent.concl.term) .prop (constantInstanceSchema result substitution) := by
  have different : result.output.constant ≠ Const.equality := by
    rw [(ConstantAdmission.source_equation accepted).1]
    intro same
    cases (Const.mk.inj same).2
  rw [(ConstantAdmission.source_equation accepted).2.2]
  simp only [CanonicalTerm.equalityDB, CanonicalTerm.constant,
    TermSubst.applyDB_app, TermSubst.applyDB_const, TypeSubst.apply_equality]
  unfold constantInstanceSchema
  apply TranslatesCompositionally.equalityDB rfl
  · exact TranslatesCompositionally.constant (constant := result.output.constant)
      (annotation := substitution.apply result.definition.ty)
      (by simp [equalityOperand?, Const.same_eq_true_iff, different]) rfl
  · exact ConstantAdmission.instanceBody_translated result substitution

theorem constantSchema_type_image {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (parameter : Name)
    (equalityRegistered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (substitution : TypeSubst) :
    HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema result) =
      constantInstanceSchema result substitution := by
  have mapped := (constantSchema_translated accepted).applyDB (TypeCorrectTermSubstitution.ofTypes substitution)
  rw [targetMap_eq_typeMap (constantSchema_ordinary accepted parameter equalityRegistered)] at mapped
  exact TranslatesCompositionally.unique_eq mapped (constantInstanceSchema_translated accepted substitution)

theorem constantInstanceSchema_models_iff (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (result : ContextConstantDefinitionResult) (substitution : TypeSubst) :
    model.models (constantInstanceSchema result substitution) ↔
      model.constDen (.constant result.output.constant (substitution.apply result.definition.ty) rfl) =
        model.denote (ConstantAdmission.instanceBody result substitution) (fun v => nomatch v) := by
  constructor
  · intro holds
    change model.Eqv (substitution.apply result.definition.ty).toHOL _ _ at holds
    have same := (model.eqv_iff_eq_of_fullDomains full _ _).mp holds
    exact same.trans (model.denote_closed_valuation_eq _ _ _)
  · intro same
    change model.Eqv (substitution.apply result.definition.ty).toHOL _ _
    apply (model.eqv_iff_eq_of_fullDomains full _ _).mpr
    exact same.trans (model.denote_closed_valuation_eq _ _ _)

theorem constant_value_of_schema {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (parameter : Name)
    (equalityRegistered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
    (substitution : TypeSubst)
    (holds : model.models (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema result))) :
    model.constDen (.constant result.output.constant (substitution.apply result.definition.ty) rfl) =
      model.denote (ConstantAdmission.instanceBody result substitution) (fun v => nomatch v) := by
  rw [constantSchema_type_image accepted parameter equalityRegistered substitution] at holds
  exact (constantInstanceSchema_models_iff model full result substitution).mp holds

theorem constant_value_of_source {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (parameter : Name)
    (equalityRegistered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
    (substitution : TypeSubst)
    (holds : model.models (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema result)))
    {type : HOL.Ty AtomicTy} {target : HOL.ClosedTerm Symbol type}
    (translated : Translates []
      ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB (source.toDB [])) type target) :
    HEq (model.constDen (.constant result.output.constant (substitution.apply result.definition.ty) rfl))
      (model.denote target (fun v => nomatch v)) := by
  have sourceChecked := (checkSource_sound _ _ (admitConstantInTheory_result accepted).1).1
  have sameBody := (SourceTerm.check_eq_some_iff _ _).mp sourceChecked
  rw [sameBody] at translated
  change Translates [] (ConstantAdmission.instanceTerm result substitution).term type target at translated
  have value := constant_value_of_schema accepted parameter equalityRegistered model full substitution holds
  refine (heq_of_eq value).trans ?_
  exact HEq.symm (translated.denote_heq_compositional
    (ConstantAdmission.instanceBody_translated result substitution) model full (fun v => nomatch v))

theorem constant_meaning_of_source {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (parameter : Name)
    (equalityRegistered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
    (substitution : TypeSubst)
    (holds : model.models (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema result)))
    (annotation : Ty) {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type)
    (publicInstance : annotation = substitution.apply result.definition.ty)
    {target : HOL.ClosedTerm Symbol type}
    (translated : Translates []
      ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB (source.toDB [])) type target) :
    model.constDen (.constant result.output.constant annotation typed) =
      model.denote target (fun v => nomatch v) := by
  subst annotation
  cases typed
  exact eq_of_heq (constant_value_of_source accepted parameter equalityRegistered model full substitution holds translated)

namespace ConstantHistory

/-- Original constant rows retain the same compositional schema translation. -/
theorem record_translated {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records) :
    TranslatesCompositionally [] result.output.definitionTheorem.sequent.concl.term .prop
      (constantSchema result) := by
  induction history with
  | nil => simp [DefinitionHistoryModels.ConstantHistory.records] at member
  | snoc prior instances name source added accepted ih =>
      simp only [DefinitionHistoryModels.ConstantHistory.records, List.mem_append,
        List.mem_singleton] at member
      rcases member with earlier | rfl
      · exact ih earlier
      · exact constantSchema_translated accepted

theorem record_licensed {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final) (primitives : Primitives initial)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records) :
    LicensedSchema final.signature (constantSchema result) := by
  refine ⟨[], _, _, record_translated history member, ?_, ContextFormed.nil _, rfl⟩
  have derived := MixedDefinitionHistory.constant_record_derives history primitives emptyAxiomPolicy
    (List.mem_map.mpr ⟨result, member, rfl⟩)
  exact derived.wellFormed.1.1

theorem record_ordinary {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final) (primitives : Primitives initial)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records) :
    OrdinarySymbols (constantSchema result) := by
  induction history with
  | nil => simp [DefinitionHistoryModels.ConstantHistory.records] at member
  | snoc prior instances name source added accepted ih =>
      simp only [DefinitionHistoryModels.ConstantHistory.records, List.mem_append,
        List.mem_singleton] at member
      rcases member with earlier | rfl
      · exact ih earlier
      · exact constantSchema_ordinary accepted primitives.equalityParameter
          (prior.includes.2 _ _ primitives.equalityRegistered)

theorem record_models {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records) :
    (history.extendModel model).models (constantSchema result) :=
  history.models_record_equation model member TypeSubst.empty
    ((record_translated history member).of_term_eq (TermSubst.typeInstance_identity _).symm)

end ConstantHistory

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

/-! Constant-only semantic extension laws retain their exact instance and
independence premises. They do not authorize repeating declaration commands. -/

theorem constant_extension_eq_of_instances
    {before : TheoryContext} {instances : InstanceWitnesses} {name : Name}
    {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory before instances name source = some result)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (meaning : ∀ substitution : TypeSubst,
      model.constDen (.constant result.output.constant (substitution.apply result.definition.ty) rfl) =
        model.denote (ConstantAdmission.instanceBody result substitution) (fun v => nomatch v)) :
    ConstantAdmission.sourceExtension result model = model := by
  rw [ConstantAdmission.sourceExtension_eq_reduct]
  apply HOL.HenkinModel.ext_data (M := model.constantSubstitutionReduct (ConstantAdmission.sourceExpansion result))
    (N := model) rfl
  · rfl
  · apply heq_of_eq
    funext type symbol
    dsimp only [HOL.HenkinModel.constantSubstitutionReduct, HOL.HenkinModel.constantSubstitutionPreModel]
    change model.denote (ConstantAdmission.sourceExpansion result symbol) _ = model.constDen symbol
    cases symbol with
    | «variable» sourceVar typed =>
      rw [ConstantAdmission.sourceExpansion_variable]
      rfl
    | constant constant annotation typed =>
      by_cases same : constant = result.output.constant
      · subst constant
        by_cases instanceExists : ∃ substitution : TypeSubst, substitution.apply result.definition.ty = annotation
        · obtain ⟨substitution, rfl⟩ := instanceExists
          cases typed
          rw [ConstantAdmission.sourceExpansion_instance result (ConstantAdmission.admitted_parameters_bounded accepted)]
          exact (model.denote_closed_valuation_eq _ _ _).trans (meaning substitution).symm
        · rw [ConstantAdmission.sourceExpansion_noninstance result annotation typed instanceExists]
          rfl
      · rw [ConstantAdmission.sourceExpansion_other result constant annotation typed same]
        rfl

theorem constant_extension_eq_of_schema
    {before : TheoryContext} {instances : InstanceWitnesses} {name : Name}
    {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory before instances name source = some result)
    (parameter : Name)
    (registered : before.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
    (holds : ∀ substitution : TypeSubst, model.models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema result))) :
    ConstantAdmission.sourceExtension result model = model :=
  constant_extension_eq_of_instances accepted model
    (fun substitution => constant_value_of_schema accepted parameter registered model full substitution (holds substitution))

theorem sourceExpansion_idempotent
    {before : TheoryContext} {instances : InstanceWitnesses} {name : Name}
    {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory before instances name source = some result)
    {type : HOL.Ty AtomicTy} (symbol : Symbol type) :
    HOL.substConst (ConstantAdmission.sourceExpansion result)
        (ConstantAdmission.sourceExpansion result symbol) = ConstantAdmission.sourceExpansion result symbol := by
  cases symbol with
  | «variable» sourceVar typed =>
    simp only [ConstantAdmission.sourceExpansion_variable, HOL.substConst, HOL.weakenCtx_nil]
  | constant constant annotation typed =>
    by_cases same : constant = result.output.constant
    · subst constant
      by_cases instanceExists : ∃ substitution : TypeSubst, substitution.apply result.definition.ty = annotation
      · obtain ⟨substitution, rfl⟩ := instanceExists
        cases typed
        rw [ConstantAdmission.sourceExpansion_instance result (ConstantAdmission.admitted_parameters_bounded accepted)]
        exact ConstantAdmission.sourceExpansion_preserves_translation result
          (ConstantAdmission.instanceBody_translated result substitution)
          ((ConstantAdmission.admitted_body_omits_identity accepted).typeInstance substitution)
      · simp only [ConstantAdmission.sourceExpansion_noninstance result annotation typed instanceExists,
          HOL.substConst, HOL.weakenCtx_nil]
    · simp only [ConstantAdmission.sourceExpansion_other result constant annotation typed same,
        HOL.substConst, HOL.weakenCtx_nil]

theorem constant_extension_idempotent
    {before : TheoryContext} {instances : InstanceWitnesses} {name : Name}
    {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory before instances name source = some result)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ConstantAdmission.sourceExtension result (ConstantAdmission.sourceExtension result model) =
      ConstantAdmission.sourceExtension result model := by
  simp only [ConstantAdmission.sourceExtension_eq_reduct, HOL.HenkinModel.constantSubstitutionReduct_comp]
  congr 1
  funext type symbol
  exact sourceExpansion_idempotent accepted symbol


theorem constant_history_eq_of_instances {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (meaning : ∀ result ∈ history.records, ∀ substitution : TypeSubst,
      model.constDen (.constant result.output.constant (substitution.apply result.definition.ty) rfl) =
        model.denote (ConstantAdmission.instanceBody result substitution) (fun v => nomatch v)) :
    history.extendModel model = model := by
  induction history with
  | nil => rfl
  | snoc prior instances name source result accepted ih =>
    change ConstantAdmission.sourceExtension result (prior.extendModel model) = model
    rw [ih (fun old member => meaning old (List.mem_append_left _ member))]
    exact constant_extension_eq_of_instances accepted model
      (meaning result (List.mem_append_right _ (by simp)))

theorem ConstantHistory.record_instance_translated {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    {result : ContextConstantDefinitionResult} (member : result ∈ history.records)
    (substitution : TypeSubst) : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.definitionTheorem.sequent.concl.term)
      .prop (constantInstanceSchema result substitution) := by
  induction history with
  | nil => simp [DefinitionHistoryModels.ConstantHistory.records] at member
  | snoc prior instances name source added accepted ih =>
    simp only [DefinitionHistoryModels.ConstantHistory.records, List.mem_append, List.mem_singleton] at member
    rcases member with earlier | rfl
    · exact ih earlier
    · exact constantInstanceSchema_translated accepted substitution

theorem constant_history_idempotent {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains) :
    history.extendModel (history.extendModel model) = history.extendModel model := by
  apply constant_history_eq_of_instances
  intro result member substitution
  exact (constantInstanceSchema_models_iff _ (history.fullDomains model full) result substitution).mp
    (history.models_record_equation model member substitution
      (ConstantHistory.record_instance_translated history member substitution))

theorem constant_history_absorbs
    {firstInitial firstFinal secondInitial secondFinal : TheoryContext}
    (first : DefinitionHistoryModels.ConstantHistory firstInitial firstFinal)
    (second : DefinitionHistoryModels.ConstantHistory secondInitial secondFinal)
    (included : first.records ⊆ second.records)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains) :
    first.extendModel (second.extendModel model) = second.extendModel model := by
  apply constant_history_eq_of_instances
  intro result member substitution
  exact (constantInstanceSchema_models_iff _ (second.fullDomains model full) result substitution).mp
    (second.models_record_equation model (included member) substitution
      (ConstantHistory.record_instance_translated second (included member) substitution))

theorem constant_history_absorbs_prefix {initial middle final : TheoryContext}
    (first : DefinitionHistoryModels.ConstantHistory initial middle)
    (second : DefinitionHistoryModels.ConstantHistory middle final)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains) :
    first.extendModel ((first.append second).extendModel model) =
      (first.append second).extendModel model := by
  apply constant_history_absorbs first (first.append second) _ model full
  intro result member
  rw [DefinitionHistoryModels.ConstantHistory.records_append]
  exact List.mem_append_left _ member

theorem sourceExpansions_commute (first second : ContextConstantDefinitionResult)
    (firstBounded : first.definition.term.typeVariables ⊆ first.definition.ty.typeVariables)
    (secondBounded : second.definition.term.typeVariables ⊆ second.definition.ty.typeVariables)
    (different : first.output.constant ≠ second.output.constant)
    (firstIndependent : first.definition.term.OmitsConstant second.output.constant)
    (secondIndependent : second.definition.term.OmitsConstant first.output.constant)
    {type : HOL.Ty AtomicTy} (symbol : Symbol type) :
    HOL.substConst (ConstantAdmission.sourceExpansion second) (ConstantAdmission.sourceExpansion first symbol) =
      HOL.substConst (ConstantAdmission.sourceExpansion first) (ConstantAdmission.sourceExpansion second symbol) := by
  cases symbol with
  | «variable» sourceVar typed =>
    simp only [ConstantAdmission.sourceExpansion_variable, HOL.substConst, HOL.weakenCtx_nil]
  | constant constant annotation typed =>
    by_cases isFirst : constant = first.output.constant
    · subst constant
      rw [ConstantAdmission.sourceExpansion_other second _ annotation typed different]
      simp only [HOL.substConst, HOL.weakenCtx_nil]
      by_cases instanceExists : ∃ substitution : TypeSubst, substitution.apply first.definition.ty = annotation
      · obtain ⟨substitution, rfl⟩ := instanceExists
        cases typed
        rw [ConstantAdmission.sourceExpansion_instance first firstBounded]
        exact ConstantAdmission.sourceExpansion_preserves_translation second
          (ConstantAdmission.instanceBody_translated first substitution) (firstIndependent.typeInstance substitution)
      · rw [ConstantAdmission.sourceExpansion_noninstance first annotation typed instanceExists]
        simp only [HOL.substConst, ConstantAdmission.sourceExpansion_other second _ annotation typed different,
          HOL.weakenCtx_nil]
    · by_cases isSecond : constant = second.output.constant
      · subst constant
        rw [ConstantAdmission.sourceExpansion_other first _ annotation typed (Ne.symm different)]
        simp only [HOL.substConst, HOL.weakenCtx_nil]
        by_cases instanceExists : ∃ substitution : TypeSubst, substitution.apply second.definition.ty = annotation
        · obtain ⟨substitution, rfl⟩ := instanceExists
          cases typed
          rw [ConstantAdmission.sourceExpansion_instance second secondBounded]
          exact (ConstantAdmission.sourceExpansion_preserves_translation first
            (ConstantAdmission.instanceBody_translated second substitution) (secondIndependent.typeInstance substitution)).symm
        · rw [ConstantAdmission.sourceExpansion_noninstance second annotation typed instanceExists]
          simp only [HOL.substConst, ConstantAdmission.sourceExpansion_other first _ annotation typed (Ne.symm different),
            HOL.weakenCtx_nil]
      · simp only [ConstantAdmission.sourceExpansion_other first _ annotation typed isFirst,
          ConstantAdmission.sourceExpansion_other second _ annotation typed isSecond,
          HOL.substConst, HOL.weakenCtx_nil]

theorem independent_constant_extensions_commute
    {firstContext secondContext : TheoryContext} {firstInstances secondInstances : InstanceWitnesses}
    {firstName secondName : Name} {firstSource secondSource : SourceTerm}
    {first second : ContextConstantDefinitionResult}
    (firstAccepted : admitConstantInTheory firstContext firstInstances firstName firstSource = some first)
    (secondAccepted : admitConstantInTheory secondContext secondInstances secondName secondSource = some second)
    (different : first.output.constant ≠ second.output.constant)
    (firstIndependent : first.definition.term.OmitsConstant second.output.constant)
    (secondIndependent : second.definition.term.OmitsConstant first.output.constant)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ConstantAdmission.sourceExtension first (ConstantAdmission.sourceExtension second model) =
      ConstantAdmission.sourceExtension second (ConstantAdmission.sourceExtension first model) := by
  simp only [ConstantAdmission.sourceExtension_eq_reduct, HOL.HenkinModel.constantSubstitutionReduct_comp]
  congr 1
  funext type symbol
  exact sourceExpansions_commute first second
    (ConstantAdmission.admitted_parameters_bounded firstAccepted)
    (ConstantAdmission.admitted_parameters_bounded secondAccepted)
    different firstIndependent secondIndependent symbol

theorem constantSchema_payload_eq {first second : ContextConstantDefinitionResult}
    (definition : first.definition = second.definition) (output : first.output = second.output) :
    constantSchema first = constantSchema second := by
  cases first
  cases second
  dsimp only at definition output
  cases definition
  cases output
  rfl

theorem constantExtension_payload_eq {first second : ContextConstantDefinitionResult}
    (definition : first.definition = second.definition) (output : first.output = second.output)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ConstantAdmission.sourceExtension first model = ConstantAdmission.sourceExtension second model := by
  cases first
  cases second
  dsimp only at definition output
  cases definition
  cases output
  simp only [ConstantAdmission.sourceExtension_eq_reduct]
  congr 1

theorem admitted_same_identity_payload
    {firstContext secondContext : TheoryContext} {firstInstances secondInstances : InstanceWitnesses}
    {firstName secondName : Name} {firstSource secondSource : SourceTerm}
    {first second : ContextConstantDefinitionResult}
    (firstAccepted : admitConstantInTheory firstContext firstInstances firstName firstSource = some first)
    (secondAccepted : admitConstantInTheory secondContext secondInstances secondName secondSource = some second)
    (same : first.output.constant = second.output.constant) :
    first.definition = second.definition ∧ first.output = second.output := by
  rw [(ConstantAdmission.source_equation firstAccepted).1,
    (ConstantAdmission.source_equation secondAccepted).1] at same
  obtain ⟨names,origins⟩ := Const.mk.inj same
  injection origins with sources
  cases names
  cases sources
  exact admitConstantInTheory_payload_eq firstAccepted secondAccepted

end Mettapedia.Languages.HOLLight.DefinitionHistorySchemas
