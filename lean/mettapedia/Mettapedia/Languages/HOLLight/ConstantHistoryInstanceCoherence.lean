import Mettapedia.Languages.HOLLight.ModelInstanceCoherence

/-!
# Type instances of original constant-definition histories

Actual source constant admission and the source type reduct commute on the
licensed source language. The comparison retains the original polymorphic
definition bodies and their declaration-instance evidence. Primitive equality
and selection require their original declaration schemas: malformed symbol
annotations may otherwise acquire primitive recognition after substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ConstantHistoryInstanceCoherence

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence

universe w

/-- An instance of the original equality declaration has its actual equality
operand shape before any further type substitution. -/
theorem declared_equality_instance (signature : Signature) (parameter : Name)
    (registered : signature.constants Const.equality = some (Ty.equality (.var parameter)))
    {annotation : Ty} (declared : ConstantInstance signature Const.equality annotation) :
    ∃ operand, annotation = Ty.equality operand := by
  obtain ⟨schema, substitution, found, equal⟩ := declared
  have schemaEq : schema = Ty.equality (.var parameter) :=
    Option.some.inj (found.symm.trans registered)
  subst schema
  exact ⟨substitution.apply (.var parameter), equal.symm.trans (TypeSubst.apply_equality _ _)⟩

/-- Original declaration admission prevents equality recognition from first
appearing at a later type instance. -/
theorem ordinary_constant_ne_equality (signature : Signature) (parameter : Name)
    (registered : signature.constants Const.equality = some (Ty.equality (.var parameter)))
    {constant : Const} {annotation : Ty}
    (declared : ConstantInstance signature constant annotation)
    (unrecognized : equalityOperand? constant annotation = none) : constant ≠ Const.equality := by
  intro equal
  subst constant
  obtain ⟨operand, rfl⟩ := declared_equality_instance signature parameter registered declared
  rw [equalityOperand?_equality] at unrecognized
  cases unrecognized

/-- Retyping the compositional translation agrees with the actual source
type substitution on every originally admitted term, including equality,
bound variables, applications and abstractions. -/
theorem translation_type_instance (signature : Signature) (parameter : Name)
    (registered : signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (substitution : TypeSubst)
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type}
    (translation : TranslatesCompositionally context term type target)
    (formed : AnnotationsFormed signature term) :
    TranslatesCompositionally (context.map (HOL.Ty.substitute substitution.baseInstance))
      ((TermSubst.mk substitution []).applyDB term)
      (HOL.Ty.substitute substitution.baseInstance type)
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance target) := by
  induction translation with
  | @equality context head annotation operand targetType recognized typed =>
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
      rw [TermSubst.applyDB_const, TypeSubst.apply_equality]
      exact .equality (equalityOperand?_equality _)
        (by rw [← typed, TypeSubst.substitute_toHOL])
  | @constant context head annotation targetType unrecognized typed =>
      cases formed with
      | constant annotationFormed declared =>
          have different := ordinary_constant_ne_equality signature parameter registered declared unrecognized
          rw [TermSubst.applyDB_const]
          apply TranslatesCompositionally.constant
          · simp [equalityOperand?, Const.same_eq_true_iff, different]
  | free typed =>
      simp only [TermSubst.applyDB, TermSubst.lookup, List.find?, Option.map]
      exact .free (by rw [← typed, TypeSubst.substitute_toHOL]; rfl)
  | bound index =>
      rw [TermSubst.applyDB_bound]
      have translated := TranslatesCompositionally.bound (index.mapTypes substitution.baseInstance)
      rw [deBruijnIndex_mapTypes] at translated
      exact translated
  | app functionTranslation argumentTranslation functionIH argumentIH =>
      cases formed with
      | app functionFormed argumentFormed =>
          rw [TermSubst.applyDB_app]
          exact .app (functionIH functionFormed) (argumentIH argumentFormed)
  | abs typed bodyTranslation bodyIH =>
      cases formed with
      | abs domainFormed bodyFormed =>
          rw [TermSubst.applyDB_abs]
          exact .abs (by rw [← typed, TypeSubst.substitute_toHOL]) (bodyIH bodyFormed)

/-- The actual body of an admitted public instance follows the same original
type substitution, rather than an unrelated replacement term. -/
theorem instanceBody_mapTypes
    {context : DefinitionAdapters.TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : DefinitionAdapters.ContextConstantDefinitionResult}
    (accepted : DefinitionAdapters.admitConstantInTheory context instances name source = some result)
    (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (first second : TypeSubst)
    (formed : TypeFormed context.signature (first.apply result.definition.ty)) :
    HEq (HOL.mapTypes second.baseInstance second.symbolInstance (ConstantAdmission.instanceBody result first))
      (ConstantAdmission.instanceBody result (first.compose second)) := by
  have translated := translation_type_instance context.signature parameter registered second
    (ConstantAdmission.instanceBody_translated result first)
    (admitted_instance_body_formed accepted first formed)
  exact (translated.unique
    ((ConstantAdmission.instanceBody_translated result (first.compose second)).of_term_eq
      (TermSubst.typeInstance_composition first second result.definition.term).symm)).2

/-- Equal indexed closed terms have the same actual value; empty-context
valuation functions do not introduce a further assumption. -/
theorem denote_closed_heq (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    {firstType secondType : HOL.Ty AtomicTy} (sameType : firstType = secondType)
    {first : HOL.ClosedTerm Symbol firstType} {second : HOL.ClosedTerm Symbol secondType}
    (sameTerm : HEq first second) (firstValuation secondValuation : M.Valuation []) :
    HEq (M.denote first firstValuation) (M.denote second secondValuation) := by
  cases sameType
  have same := eq_of_heq sameTerm
  subst second
  exact heq_of_eq (HOL.HenkinModel.denote_closed_valuation_eq M first firstValuation secondValuation)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the original instance in the actual type reduct gives the
value of the composed source instance in the original model. -/
theorem denote_instanceBody_reindex
    {context : DefinitionAdapters.TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : DefinitionAdapters.ContextConstantDefinitionResult}
    (accepted : DefinitionAdapters.admitConstantInTheory context instances name source = some result)
    (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (first second : TypeSubst)
    (formed : TypeFormed context.signature (first.apply result.definition.ty)) :
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
  · exact instanceBody_mapTypes accepted parameter registered first second formed

/-- The original source extension equation also applies when the annotation
and its target HOL type are represented by explicit equalities. -/
theorem sourceExtension_constant_instance_heq (result : DefinitionAdapters.ContextConstantDefinitionResult)
    (bounded : result.definition.term.typeVariables ⊆ result.definition.ty.typeVariables)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (substitution : TypeSubst)
    {annotation : Ty} (instanceEq : annotation = substitution.apply result.definition.ty)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type) :
    HEq ((ConstantAdmission.sourceExtension result M).constDen
      (.constant result.output.constant annotation typed))
      (M.denote (ConstantAdmission.instanceBody result substitution) (fun index => nomatch index)) := by
  subst annotation
  cases typed
  exact heq_of_eq (ConstantAdmission.sourceExtension_constant_instance result bounded M substitution)

/-- An original free-variable symbol is unaffected by a constant-only
admission, with its source annotation retained. -/
theorem sourceExtension_variable (result : DefinitionAdapters.ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (sourceVar : SourceVar)
    {type : HOL.Ty AtomicTy} (typed : sourceVar.ty.toHOL = type) :
    (ConstantAdmission.sourceExtension result M).constDen (.variable sourceVar typed) =
      M.constDen (.variable sourceVar typed) := by
  unfold ConstantAdmission.sourceExtension ConstantAdmission.sourcePreModel ConstantAdmission.sourceMeanings
  change M.denote (ConstantAdmission.sourceExpansion result (.variable sourceVar typed))
    (fun index => nomatch index) = _
  rw [ConstantAdmission.sourceExpansion_variable]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- One original polymorphic constant admission commutes with type reduct
on every licensed source instance of the resulting declaration context. -/
theorem sourceExtension_reindex_agreement
    {context : DefinitionAdapters.TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : DefinitionAdapters.ContextConstantDefinitionResult}
    (accepted : DefinitionAdapters.admitConstantInTheory context instances name source = some result)
    (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (substitution : TypeSubst) :
    SourceAgreement result.context.signature
      (ConstantAdmission.sourceExtension result (reindexedModel substitution M))
      (reindexedModel substitution (ConstantAdmission.sourceExtension result M)) := by
  have signatureEq := admitted_constant_signature accepted
  have operators : result.context.signature.typeOperators = context.signature.typeOperators := by
    rw [signatureEq]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    rfl
  · intro constant annotation type typed formed declared
    have priorFormed := (typeFormed_eq_of_operators result.context.signature context.signature operators annotation).mp formed
    by_cases newConstant : constant = result.output.constant
    · subst constant
      obtain ⟨schema, first, found, equal⟩ := declared
      have row := (DefinitionAdapters.admitConstantInTheory_result accepted).2.2.2.2.2.1
      have schemaEq : schema = result.definition.ty := Option.some.inj (found.symm.trans row)
      subst schema
      subst annotation
      cases typed
      rw [ConstantAdmission.sourceExtension_constant_instance result
        (ConstantAdmission.admitted_parameters_bounded accepted)]
      change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance M.Carrier _).symm
        ((ConstantAdmission.sourceExtension result M).constDen
          (substitution.symbolInstance (.constant result.output.constant (first.apply result.definition.ty) rfl))))
      refine (denote_instanceBody_reindex accepted parameter registered M full first substitution priorFormed).trans ?_
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

/-- Actual licensed-source comparison composes through transported carriers
and symbol values. -/
theorem sourceAgreement_trans {signature : Signature}
    {first second third : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (firstSecond : SourceAgreement signature first second)
    (secondThird : SourceAgreement signature second third) : SourceAgreement signature first third where
  carriers := fun type formed => (firstSecond.carriers type formed).trans (secondThird.carriers type formed)
  constants := fun constant annotation {_} typed formed declared =>
    (firstSecond.constants constant annotation typed formed declared).trans
      (secondThird.constants constant annotation typed formed declared)
  variableValues := fun sourceVar {_} typed formed =>
    (firstSecond.variableValues sourceVar typed formed).trans (secondThird.variableValues sourceVar typed formed)

/-- Every actual original constant-definition history commutes with the
source type reduct on its licensed final language. No type-coherence property
of the initial model is assumed. -/
theorem constantHistory_reindex_agreement {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (parameter : Name)
    (registered : initial.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (substitution : TypeSubst) :
    SourceAgreement final.signature (history.extendModel (reindexedModel substitution M))
      (reindexedModel substitution (history.extendModel M)) := by
  induction history with
  | nil =>
      exact ⟨fun _ _ => rfl, fun _ _ {_} _ _ _ => HEq.rfl, fun _ {_} _ _ => HEq.rfl⟩
  | snoc prior instances name source result accepted ih =>
      have compared := ih.constantExtension accepted
        (prior.includes.1 TypeOp.function 2 functionArity)
        (prior.fullDomains _ (reindexedModel_fullDomains substitution M))
        (reindexedModel_fullDomains substitution _)
      exact sourceAgreement_trans compared
        (sourceExtension_reindex_agreement accepted parameter
          (prior.includes.2 Const.equality _ registered)
          (prior.extendModel M) (prior.fullDomains M full) substitution)

/-- The constructed source-domain family supplies the initial licensed
comparison with the actual type reduct. The original selection schema fixes
the source operand before instantiation. -/
theorem initial_reindex_agreement (signature : Signature) (parameter : Name)
    (registered : signature.constants selectionConstant = some (selectionType (.var parameter)))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement signature
      (initialModel other (reindex (primitiveFamilies other) substitution assignment))
      (reindexedModel substitution (initialModel other assignment)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro targetType targetFormed
    have reductCarrier : (reindexedModel substitution (initialModel other assignment)).Carrier =
        atomicCarrier other (reindex (primitiveFamilies other) substitution assignment) := by
      simpa only [initialModel, ModelInterpretation.model] using reindexedModel_carrier other assignment
        (interpretation other assignment (domainMeanings other assignment)) substitution
    change HOL.Ty.denote (atomicCarrier other (reindex (primitiveFamilies other) substitution assignment)) targetType = _
    rw [reductCarrier]
  · intro constant annotation targetType typed annotationFormed declared
    change HEq ((initialModel other (reindex (primitiveFamilies other) substitution assignment)).constDen
      (.constant constant annotation typed))
      ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance (initialModel other assignment).Carrier targetType).symm
        ((initialModel other assignment).constDen (substitution.symbolInstance (.constant constant annotation typed))))
    exact (initial_constant_instance signature parameter registered other assignment substitution
      constant annotation declared typed).trans (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm
  · intro sourceVar targetType typed variableFormed
    change HEq ((initialModel other (reindex (primitiveFamilies other) substitution assignment)).constDen
      (.variable sourceVar typed))
      ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance (initialModel other assignment).Carrier targetType).symm
        ((initialModel other assignment).constDen (substitution.symbolInstance (.variable sourceVar typed))))
    exact (initial_variable_instance other assignment substitution sourceVar typed).trans
      (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm

/-- Complete admitted constant histories built from the actual coherent
source-domain family obey the source type-instance law. -/
theorem constantHistory_instance_agreement {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionRegistered : initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement final.signature
      (history.extendModel (initialModel other (reindex (primitiveFamilies other) substitution assignment)))
      (reindexedModel substitution (history.extendModel (initialModel other assignment))) :=
  sourceAgreement_trans
    ((initial_reindex_agreement initial.signature selectionParameter selectionRegistered other assignment substitution).constantHistory
      history functionArity (initialModel_fullDomains _ _) (reindexedModel_fullDomains _ _))
    (constantHistory_reindex_agreement history functionArity equalityParameter equalityRegistered
      (initialModel other assignment) (initialModel_fullDomains _ _) substitution)

/-- Every original formed sentence over the complete admitted constant
history has the truth of its actual source type instance. -/
theorem constantHistory_models_instance {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionRegistered : initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed final.signature term) :
    (history.extendModel (initialModel other (reindex (primitiveFamilies other) substitution assignment))).models formula ↔
      (history.extendModel (initialModel other assignment)).models
        (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula) := by
  have comparison := constantHistory_instance_agreement history functionArity equalityParameter equalityRegistered
    selectionParameter selectionRegistered other assignment substitution
  exact (comparison.models (history.includes.1 TypeOp.function 2 functionArity)
      (history.fullDomains _ (initialModel_fullDomains _ _)) (reindexedModel_fullDomains _ _)
      translation formed).trans
    (reindexedModel_models substitution _ (history.fullDomains _ (initialModel_fullDomains _ _)) formula)

/-- Restrict a checked model comparison to the original included language. -/
theorem sourceAgreement_restrict {original extended : Signature}
    (included : original.Includes extended)
    {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (agreement : SourceAgreement extended first second) : SourceAgreement original first second where
  carriers := fun type formed => agreement.carriers type (formed.mono included)
  constants := fun constant annotation {_} typed formed declared =>
    agreement.constants constant annotation typed (formed.mono included) (declared.mono included)
  variableValues := fun sourceVar {_} typed formed =>
    agreement.variableValues sourceVar typed (formed.mono included)

/-- When the original language has no selection declaration, all its licensed
symbols still obey the initial type-instance comparison. An auxiliary
signature extension is used only to invoke the already checked selection
schema law; neither model nor submitted language is changed. -/
theorem initial_reindex_unregistered_selection (signature : Signature) (parameter : Name)
    (unregistered : signature.constants selectionConstant = none)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement signature
      (initialModel other (reindex (primitiveFamilies other) substitution assignment))
      (reindexedModel substitution (initialModel other assignment)) := by
  apply sourceAgreement_restrict (signature.includes_addConstant selectionConstant
    (selectionType (.var parameter)) unregistered)
  apply initial_reindex_agreement (signature.addConstant selectionConstant (selectionType (.var parameter)))
    parameter
  simp [Signature.addConstant]

/-- The complete constructed history law also covers languages with no
original selection declaration, as well as the declared polymorphic selector. -/
theorem constantHistory_instance_agreement_optional_selection
    {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement final.signature
      (history.extendModel (initialModel other (reindex (primitiveFamilies other) substitution assignment)))
      (reindexedModel substitution (history.extendModel (initialModel other assignment))) := by
  rcases selectionDeclaration with unregistered | registered
  · exact sourceAgreement_trans
      ((initial_reindex_unregistered_selection initial.signature selectionParameter unregistered other assignment substitution).constantHistory
        history functionArity (initialModel_fullDomains _ _) (reindexedModel_fullDomains _ _))
      (constantHistory_reindex_agreement history functionArity equalityParameter equalityRegistered
        (initialModel other assignment) (initialModel_fullDomains _ _) substitution)
  · exact constantHistory_instance_agreement history functionArity equalityParameter equalityRegistered
      selectionParameter registered other assignment substitution

/-- Original sentence truth follows the complete constant-history type
instance, including the original core language without a selector row. -/
theorem constantHistory_models_instance_optional_selection
    {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed final.signature term) :
    (history.extendModel (initialModel other (reindex (primitiveFamilies other) substitution assignment))).models formula ↔
      (history.extendModel (initialModel other assignment)).models
        (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula) := by
  have comparison := constantHistory_instance_agreement_optional_selection history functionArity
    equalityParameter equalityRegistered selectionParameter selectionDeclaration other assignment substitution
  exact (comparison.models (history.includes.1 TypeOp.function 2 functionArity)
      (history.fullDomains _ (initialModel_fullDomains _ _)) (reindexedModel_fullDomains _ _)
      translation formed).trans
    (reindexedModel_models substitution _ (history.fullDomains _ (initialModel_fullDomains _ _)) formula)

namespace Controls

open DefinitionAdapters.ContextControls

theorem core_equality_registered : coreContext.signature.constants Const.equality =
    some (Ty.equality (.var equalityParameter)) := by
  simp [coreContext, DefinitionAdapters.TheoryContext.addConstant, Signature.addConstant]

theorem core_selection_unregistered : coreContext.signature.constants selectionConstant = none := by
  decide +kernel

def equalityRecognitionInstance : TypeSubst :=
  ⟨[(equalityParameter, Ty.equality Ty.bool)]⟩

/-- Raw annotations can acquire primitive equality recognition only after
substitution. The original declaration licence rules out this input. -/
theorem equality_recognition_requires_original_licence :
    equalityOperand? Const.equality (.var equalityParameter) = none ∧
      equalityOperand? Const.equality
        (equalityRecognitionInstance.apply (.var equalityParameter)) = some Ty.bool := by
  constructor
  · simp [equalityOperand?, Ty.destFunction?]
  · have instanceEq : equalityRecognitionInstance.apply (.var equalityParameter) = Ty.equality Ty.bool :=
      (Ty.same_eq_true_iff _ _).mp (by decide +kernel)
    rw [instanceEq, equalityOperand?_equality]

theorem malformed_equality_not_declared (signature : Signature)
    (registered : signature.constants Const.equality = some (Ty.equality (.var equalityParameter))) :
    ¬ ConstantInstance signature Const.equality (.var equalityParameter) := by
  intro declared
  obtain ⟨operand, same⟩ := declared_equality_instance signature equalityParameter registered declared
  cases same

theorem malformed_equality_annotation_refused :
    constantInstanceB coreContext.signature equalityCertificates Const.equality (.var equalityParameter) = false := by
  decide +kernel

/-- The complete original two-definition history, including the alias that
depends on its predecessor, commutes with the actual source type reduct. -/
theorem polymorphic_history_reduct
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (substitution : TypeSubst) :
    SourceAgreement DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
      (DefinitionHistoryModels.Controls.polymorphicDefinitions.extendModel (reindexedModel substitution M))
      (reindexedModel substitution (DefinitionHistoryModels.Controls.polymorphicDefinitions.extendModel M)) :=
  constantHistory_reindex_agreement DefinitionHistoryModels.Controls.polymorphicDefinitions
    (core_includes.1 TypeOp.function 2 function_registered) equalityParameter core_equality_registered
    M full substitution

theorem polymorphic_alias_type_formed :
    TypeFormed DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
      DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty := by
  apply (typeFormedB_eq_true_iff _ _).mp
  decide +kernel

theorem polymorphic_alias_instance_registered :
    ConstantInstance DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
      DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
      DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty := by
  refine ⟨_, TypeSubst.empty, ?_, TypeSubst.apply_empty _⟩
  exact (DefinitionAdapters.admitConstantInTheory_result
    (Option.some_get DefinitionHistoryModels.Controls.polymorphic_alias_admission).symm).2.2.2.2.2.1

/-- The actual admitted polymorphic alias follows every source type
substitution in the constructed whole-history model, including substitutions
to compound function types. -/
theorem polymorphic_alias_instance (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (substitution : TypeSubst) :
    HEq ((DefinitionHistoryModels.Controls.polymorphicDefinitions.extendModel
      (initialModel other (reindex (primitiveFamilies other) substitution assignment))).constDen
        (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
          DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty rfl))
      ((DefinitionHistoryModels.Controls.polymorphicDefinitions.extendModel
        (initialModel other assignment)).constDen
        (substitution.symbolInstance
          (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
            DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty rfl))) := by
  have compared := constantHistory_instance_agreement_optional_selection
    DefinitionHistoryModels.Controls.polymorphicDefinitions
    (core_includes.1 TypeOp.function 2 function_registered) equalityParameter core_equality_registered
    equalityParameter (Or.inl core_selection_unregistered) other assignment substitution
  exact (compared.constants _ _ rfl polymorphic_alias_type_formed polymorphic_alias_instance_registered).trans
    (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _)

/-- Wrong public annotations remain outside the registered schema, even
though a raw symbol may still be stored as syntax. -/
theorem malformed_polymorphic_alias_refused :
    constantInstanceB DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
      certificates
      DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant Ty.bool = false := by
  decide +kernel

end Controls

end Mettapedia.Languages.HOLLight.ConstantHistoryInstanceCoherence
