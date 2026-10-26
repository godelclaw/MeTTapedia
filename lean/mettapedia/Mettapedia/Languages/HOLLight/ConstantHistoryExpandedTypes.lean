import Mettapedia.Languages.HOLLight.UniformTypeDefinitionSupport

/-!
# Original constant histories over subsequently extended type tables

The original constant rows and admission receipts are retained. A later
registered type table permits old declaration instances at newly formed
carrier types, without requiring those instances to have been formed in the
predecessor type table. The original type reduct and defining bodies remain
the semantic operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ConstantHistoryExpandedTypes

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters ConstantHistoryInstanceCoherence

universe w

/-- The actual old constant table is compared over the supplied later type
table. This changes formation scope, not admitted declarations or meanings. -/
def withTypes (original later : Signature) : Signature :=
  { original with typeOperators := later.typeOperators }

theorem withTypes_includes (original later : Signature)
    (types : ∀ operator arity, original.typeOperators operator = some arity →
      later.typeOperators operator = some arity) : original.Includes (withTypes original later) :=
  ⟨types, fun _ _ found => found⟩

theorem history_typeOperators {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final) :
    final.signature.typeOperators = initial.signature.typeOperators := by
  induction history with
  | nil => rfl
  | snoc prior instances name source result accepted ih =>
      rw [admitted_constant_signature accepted]
      exact ih

theorem withTypes_admitted_constant
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (later : Signature) : withTypes result.context.signature later =
      (withTypes context.signature later).addConstant result.output.constant result.definition.ty := by
  rw [admitted_constant_signature accepted]
  rfl

/-- Formation of the defining instance is earned from the original accepted
body, its hidden-parameter guard and the later public type annotation. -/
theorem admitted_instance_body_formed
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (later : Signature)
    (types : ∀ operator arity, context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (substitution : TypeSubst)
    (publicFormed : TypeFormed (withTypes context.signature later) (substitution.apply result.definition.ty)) :
    AnnotationsFormed (withTypes context.signature later) (ConstantAdmission.instanceTerm result substitution).term := by
  apply annotations_instance_formed_supported
    (withTypes context.signature later) substitution
    (((checkSource_sound _ _ (admitConstantInTheory_result accepted).1).2).mono
      (withTypes_includes context.signature later types))
  intro parameter occurs
  exact formed_instance_parameter _ substitution result.definition.ty publicFormed parameter
    (ConstantAdmission.admitted_parameters_bounded accepted occurs)

theorem instanceBody_mapTypes
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (later : Signature)
    (types : ∀ operator arity, context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (first second : TypeSubst)
    (formed : TypeFormed (withTypes context.signature later) (first.apply result.definition.ty)) :
    HEq (HOL.mapTypes second.baseInstance second.symbolInstance (ConstantAdmission.instanceBody result first))
      (ConstantAdmission.instanceBody result (first.compose second)) := by
  have translated := translation_type_instance (withTypes context.signature later) parameter registered second
    (ConstantAdmission.instanceBody_translated result first)
    (admitted_instance_body_formed accepted later types first formed)
  exact (translated.unique
    ((ConstantAdmission.instanceBody_translated result (first.compose second)).of_term_eq
      (TermSubst.typeInstance_composition first second result.definition.term).symm)).2

set_option backward.isDefEq.respectTransparency false in
theorem denote_instanceBody_reindex
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (later : Signature)
    (types : ∀ operator arity, context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (first second : TypeSubst)
    (formed : TypeFormed (withTypes context.signature later) (first.apply result.definition.ty)) :
    HEq ((reindexedModel second M).denote (ConstantAdmission.instanceBody result first)
      (fun index => nomatch index))
      (M.denote (ConstantAdmission.instanceBody result (first.compose second))
        (fun index => nomatch index)) := by
  let valuation : M.Valuation ([].map (HOL.Ty.substitute second.baseInstance)) :=
    fun index => nomatch index
  have preserved := HOL.HenkinModel.denote_mapTypes second.baseInstance second.symbolInstance M full
    (ConstantAdmission.instanceBody result first) valuation
  have normalized := HOL.HenkinModel.denote_closed_valuation_eq (reindexedModel second M)
    (ConstantAdmission.instanceBody result first) (fun index => nomatch index)
    (HOL.HenkinModel.typeReductValuation second.baseInstance second.symbolInstance M valuation)
  change HOL.Ty.denoteSubstituteEquiv second.baseInstance M.Carrier _
    ((reindexedModel second M).denote (ConstantAdmission.instanceBody result first)
      (HOL.HenkinModel.typeReductValuation second.baseInstance second.symbolInstance M valuation)) =
    M.denote (HOL.mapTypes second.baseInstance second.symbolInstance (ConstantAdmission.instanceBody result first))
      valuation at preserved
  rw [← normalized] at preserved
  refine (HOL.Ty.denoteSubstituteEquiv_apply_heq _ _ _ _).symm.trans ?_
  refine (heq_of_eq preserved).trans ?_
  apply denote_closed_heq M
  · rw [TypeSubst.substitute_toHOL, TypeSubst.apply_compose]
  · exact instanceBody_mapTypes accepted later types parameter registered first second formed

set_option backward.isDefEq.respectTransparency false in
/-- An original constant extension commutes with the source type reduct at
all instances formed using the later registered type table. -/
theorem sourceExtension_reindex_agreement
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (later : Signature)
    (types : ∀ operator arity, context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (substitution : TypeSubst) :
    SourceAgreement (withTypes result.context.signature later)
      (ConstantAdmission.sourceExtension result (reindexedModel substitution M))
      (reindexedModel substitution (ConstantAdmission.sourceExtension result M)) := by
  have signatureEq := withTypes_admitted_constant accepted later
  have operators : (withTypes result.context.signature later).typeOperators =
      (withTypes context.signature later).typeOperators := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    rfl
  · intro constant annotation type typed formed declared
    have priorFormed := (typeFormed_eq_of_operators _ _ operators annotation).mp formed
    by_cases newConstant : constant = result.output.constant
    · subst constant
      obtain ⟨schema, first, found, equal⟩ := declared
      have row := (admitConstantInTheory_result accepted).2.2.2.2.2.1
      have schemaEq : schema = result.definition.ty := Option.some.inj (found.symm.trans row)
      subst schema
      subst annotation
      cases typed
      rw [ConstantAdmission.sourceExtension_constant_instance result
        (ConstantAdmission.admitted_parameters_bounded accepted)]
      change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance M.Carrier _).symm
        ((ConstantAdmission.sourceExtension result M).constDen
          (substitution.symbolInstance (.constant result.output.constant (first.apply result.definition.ty) rfl))))
      refine (denote_instanceBody_reindex accepted later types parameter registered M full first substitution priorFormed).trans ?_
      symm
      refine (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
      exact sourceExtension_constant_instance_heq result (ConstantAdmission.admitted_parameters_bounded accepted)
        M (first.compose substitution) (TypeSubst.apply_compose first substitution result.definition.ty).symm _
    · rw [ConstantAdmission.sourceExtension_constant_other result _ constant annotation typed newConstant]
      change HEq ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance M.Carrier type).symm
        (M.constDen (substitution.symbolInstance (.constant constant annotation typed))))
        ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance M.Carrier type).symm
          ((ConstantAdmission.sourceExtension result M).constDen
            (substitution.symbolInstance (.constant constant annotation typed))))
      simp only [TypeSubst.symbolInstance,
        ConstantAdmission.sourceExtension_constant_other result M constant _ _ newConstant]
      rfl
  · intro sourceVar type typed formed
    rw [sourceExtension_variable]
    change HEq ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance M.Carrier type).symm
      (M.constDen (substitution.symbolInstance (.variable sourceVar typed))))
      ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance M.Carrier type).symm
        ((ConstantAdmission.sourceExtension result M).constDen
          (substitution.symbolInstance (.variable sourceVar typed))))
    simp only [TypeSubst.symbolInstance, sourceExtension_variable]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Actual source-model agreement extends through an original constant
admission while its public instances use the larger registered type table. -/
theorem constantExtension_agreement
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (later : Signature)
    (types : ∀ operator arity, context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (agreement : SourceAgreement (withTypes context.signature later) first second)
    (firstFull : first.FullDomains) (secondFull : second.FullDomains) :
    SourceAgreement (withTypes result.context.signature later)
      (ConstantAdmission.sourceExtension result first) (ConstantAdmission.sourceExtension result second) := by
  have signatureEq := withTypes_admitted_constant accepted later
  have operators : (withTypes result.context.signature later).typeOperators =
      (withTypes context.signature later).typeOperators := rfl
  have formedBack := fun type => typeFormed_eq_of_operators
    (withTypes result.context.signature later) (withTypes context.signature later) operators type
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    exact agreement.carriers type ((formedBack _).mp formed)
  · intro constant annotation type typed formed declared
    have priorFormed := (formedBack annotation).mp formed
    by_cases newConstant : constant = result.output.constant
    · subst constant
      obtain ⟨schema, substitution, found, equal⟩ := declared
      have registered := (admitConstantInTheory_result accepted).2.2.2.2.2.1
      have schemaEq : schema = result.definition.ty := Option.some.inj (found.symm.trans registered)
      subst schema
      subst annotation
      cases typed
      rw [ConstantAdmission.sourceExtension_constant_instance result
          (ConstantAdmission.admitted_parameters_bounded accepted),
        ConstantAdmission.sourceExtension_constant_instance result
          (ConstantAdmission.admitted_parameters_bounded accepted)]
      apply agreement.denote (types TypeOp.function 2 functionArity) firstFull secondFull
        (ConstantAdmission.instanceBody_translated result substitution)
        (admitted_instance_body_formed accepted later types substitution priorFormed)
      · intro type member
        simp at member
      · intro type index
        nomatch index
    · rw [ConstantAdmission.sourceExtension_constant_other result first constant annotation typed newConstant,
        ConstantAdmission.sourceExtension_constant_other result second constant annotation typed newConstant]
      apply agreement.constants constant annotation typed priorFormed
      obtain ⟨schema, substitution, found, equal⟩ := declared
      refine ⟨schema, substitution, ?_, equal⟩
      rw [signatureEq] at found
      simpa [Signature.addConstant, Const.same_eq_true_iff, newConstant] using found
  · intro sourceVar type typed formed
    rw [ConstantAdmission.sourceExtension_eq_reduct result first,
      ConstantAdmission.sourceExtension_eq_reduct result second]
    change HEq (first.denote (ConstantAdmission.sourceExpansion result (.variable sourceVar typed))
      (fun index => nomatch index)) (second.denote (ConstantAdmission.sourceExpansion result (.variable sourceVar typed))
      (fun index => nomatch index))
    rw [ConstantAdmission.sourceExpansion_variable]
    exact agreement.variableValues sourceVar typed ((formedBack _).mp formed)

/-- The original chronological constant steps preserve agreement over the
larger type table. The same actual extension functions are used. -/
theorem history_agreement {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (later : Signature)
    (types : ∀ operator arity, initial.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (agreement : SourceAgreement (withTypes initial.signature later) first second)
    (firstFull : first.FullDomains) (secondFull : second.FullDomains) :
    SourceAgreement (withTypes final.signature later) (history.extendModel first) (history.extendModel second) := by
  induction history with
  | nil => exact agreement
  | snoc prior instances name source result accepted ih =>
      apply constantExtension_agreement accepted later _
        (prior.includes.1 TypeOp.function 2 functionArity) ih
        (prior.fullDomains first firstFull) (prior.fullDomains second secondFull)
      intro operator arity registered
      apply types operator arity
      rw [← history_typeOperators prior]
      exact registered

/-- A whole original constant history and the source type reduct commute
on old declaration instances at all later formed carrier types. -/
theorem history_reindex_agreement {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (later : Signature)
    (types : ∀ operator arity, initial.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (parameter : Name)
    (registered : initial.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (substitution : TypeSubst) :
    SourceAgreement (withTypes final.signature later)
      (history.extendModel (reindexedModel substitution M)) (reindexedModel substitution (history.extendModel M)) := by
  induction history with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ {_} _ _ _ => HEq.rfl, fun _ {_} _ _ => HEq.rfl⟩
  | snoc prior instances name source result accepted ih =>
      have priorTypes : ∀ operator arity, _ = some arity → later.typeOperators operator = some arity :=
        fun operator arity found => types operator arity (by rw [← history_typeOperators prior]; exact found)
      have compared := constantExtension_agreement accepted later priorTypes
        (prior.includes.1 TypeOp.function 2 functionArity) ih
        (prior.fullDomains _ (reindexedModel_fullDomains substitution M)) (reindexedModel_fullDomains substitution _)
      exact sourceAgreement_trans compared
        (sourceExtension_reindex_agreement accepted later priorTypes parameter
          (prior.includes.2 Const.equality _ registered)
          (prior.extendModel M) (prior.fullDomains M full) substitution)

/-- The constructed coherent initial meanings, original admissions and
actual reduct jointly give the larger-type-table instance law. -/
theorem history_instance_agreement {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (later : Signature)
    (types : ∀ operator arity, initial.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement (withTypes final.signature later)
      (history.extendModel (initialModel other (reindex (primitiveFamilies other) substitution assignment)))
      (reindexedModel substitution (history.extendModel (initialModel other assignment))) := by
  have initialCompared : SourceAgreement (withTypes initial.signature later)
      (initialModel other (reindex (primitiveFamilies other) substitution assignment))
      (reindexedModel substitution (initialModel other assignment)) := by
    rcases selectionDeclaration with absent | declared
    · exact initial_reindex_unregistered_selection (withTypes initial.signature later)
        selectionParameter absent other assignment substitution
    · exact initial_reindex_agreement (withTypes initial.signature later)
        selectionParameter declared other assignment substitution
  exact sourceAgreement_trans
    (history_agreement history later types functionArity initialCompared
      (initialModel_fullDomains _ _) (reindexedModel_fullDomains _ _))
    (history_reindex_agreement history later types functionArity equalityParameter equalityRegistered
      (initialModel other assignment) (initialModel_fullDomains _ _) substitution)

namespace Controls

open UniformTypeDefinitionFamily UniformTypeDefinitionFamily.Controls DefinitionAdapters.ContextControls

/-- This is the original alias's public instance at the newly defined
Boolean carrier, not an alternative alias declaration. -/
def aliasNewCarrierAnnotation : Ty := UniformTypeDefinitionModels.Controls.nestedInstance.apply
  DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty

theorem alias_new_carrier_formed :
    TypeFormed (withTypes DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
      polymorphicResult.context.signature) aliasNewCarrierAnnotation := by
  apply (typeFormedB_eq_true_iff _ _).mp
  decide +kernel

/-- The same annotation was genuinely unavailable in the old type table. -/
theorem alias_new_carrier_not_previously_formed :
    typeFormedB DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
      aliasNewCarrierAnnotation = false := by
  decide +kernel

theorem alias_new_carrier_original_instance :
    ConstantInstance (withTypes DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
      polymorphicResult.context.signature) DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
      aliasNewCarrierAnnotation := by
  have declaration := ConstantHistoryInstanceCoherence.Controls.polymorphic_alias_instance_registered.substitute
    DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
    UniformTypeDefinitionModels.Controls.nestedInstance
  exact declaration.mono (UniformTypeDefinitionModels.comparisonSignature_includes polymorphic_result_admitted)

/-- The complete old history's actual model at a new carrier instance
commutes with every further original type substitution. -/
theorem actual_alias_new_carrier_type_instance (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (substitution : TypeSubst) :
    let actualOperators := UniformTypeDefinitionModels.operators
      DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other
    HEq ((priorModel DefinitionHistoryModels.Controls.polymorphicDefinitions actualOperators
      (reindex (primitiveFamilies actualOperators) substitution assignment)).constDen
      (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant aliasNewCarrierAnnotation rfl))
      ((reindexedModel substitution
        (priorModel DefinitionHistoryModels.Controls.polymorphicDefinitions actualOperators assignment)).constDen
        (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant aliasNewCarrierAnnotation rfl)) := by
  intro actualOperators
  have includesTypes : ∀ operator arity, coreContext.signature.typeOperators operator = some arity →
      polymorphicResult.context.signature.typeOperators operator = some arity := by
    intro operator arity found
    exact (UniformTypeDefinitionModels.comparisonSignature_includes polymorphic_result_admitted).1 operator arity
      (DefinitionHistoryModels.Controls.polymorphicDefinitions.includes.1 operator arity found)
  exact (history_instance_agreement DefinitionHistoryModels.Controls.polymorphicDefinitions
    polymorphicResult.context.signature includesTypes (core_includes.1 TypeOp.function 2 function_registered)
    equalityParameter ConstantHistoryInstanceCoherence.Controls.core_equality_registered
    equalityParameter (Or.inl ConstantHistoryInstanceCoherence.Controls.core_selection_unregistered)
    actualOperators assignment substitution).constants _ _ rfl alias_new_carrier_formed alias_new_carrier_original_instance

/-- Expanding the registered type table does not waive the original
constructor arities of instances. -/
theorem malformed_alias_instance_refused :
    typeFormedB (withTypes DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
      polymorphicResult.context.signature)
      (UniformTypeDefinitionModels.Controls.malformedInstance.apply
        DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty) = false := by
  decide +kernel

end Controls

theorem history_declared_origin {initial final : TheoryContext} (history : DefinitionHistoryModels.ConstantHistory initial final)
    (constant : Const) (schema : Ty) (declared : final.signature.constants constant = some schema) :
    initial.signature.constants constant = some schema ∨
      ∃ result ∈ history.records, constant = result.output.constant := by
  classical
  induction history with
  | nil => exact Or.inl declared
  | snoc prior instances name source added accepted ih =>
    rw [admitted_constant_signature accepted] at declared
    by_cases same : constant = added.output.constant
    · exact Or.inr ⟨added,List.mem_append_right _ (List.mem_singleton_self _),same⟩
    · have initialOrRecord := ih (by simpa [Signature.addConstant,Const.same_eq_true_iff,same] using declared)
      rcases initialOrRecord with initial | ⟨result,member,equal⟩
      · exact Or.inl initial
      · exact Or.inr ⟨result,List.mem_append_left _ member,equal⟩

end Mettapedia.Languages.HOLLight.ConstantHistoryExpandedTypes
