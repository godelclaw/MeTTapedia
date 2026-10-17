import Mettapedia.Languages.HOLLight.UniformTypeDefinitionFamily

/-!
# All original source instances of a uniform witnessed type definition

The new source symbols are interpreted in one carrier model. An instance
uses the actual domains of its original source type arguments, including
arguments containing the newly declared type. Public annotation equality
forces the same domain tuple, so interpretation is independent of a chosen
source-substitution witness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.UniformTypeDefinitionModels

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters UniformTypeDefinitionFamily

universe w

variable {initial context : TheoryContext}
  (history : DefinitionHistoryModels.ConstantHistory initial context)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

noncomputable def operators : OperatorFamilies.{w} :=
  extend other (SourceTypeDefinitionTransport.operator request) (family history accepted proof other)

noncomputable def instanceArguments (substitution : TypeSubst) : List Domain.{w} :=
  request.typeVariables.map (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment)

noncomputable def instanceAssignment (substitution : TypeSubst) : Assignment.{w} :=
  tupleAssignment request.typeVariables (instanceArguments history accepted proof other assignment substitution)

theorem instanceAssignment_agrees (substitution : TypeSubst) :
    ∀ parameter ∈ request.typeVariables,
      instanceAssignment history accepted proof other assignment substitution parameter =
        reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment parameter :=
  tupleAssignment_mapped _ _

/-- Original admission and support earn the complete represented carrier
transport. Replacement types may themselves contain the new operator. -/
theorem represented_carrier (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel history accepted proof other assignment).Carrier
      (substitution.apply result.core.witness.ty).toHOL =
    HOL.Ty.denote.{0, w + 1}
      (priorModel history other (instanceAssignment history accepted proof other assignment substitution)).Carrier
      result.core.witness.ty.toHOL := by
  rw [UniformTypeDefinitionFamily.carrierModel, priorModel_carrier, priorModel_carrier,
    ← evaluate_toHOL, ← evaluate_toHOL]
  apply congrArg Domain.Carrier
  rw [evaluate_apply]
  rw [domain_extend_formed context.signature other _ _
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted) _ _
    (SourceTypeDefinitionTransport.admitted_represented_formed accepted)]
  apply evaluate_parameter_agreement
  intro parameter member
  exact (instanceAssignment_agrees history accepted proof other assignment substitution parameter
    (List.mem_toFinset.mp (represented_support accepted member))).symm

theorem new_carrier (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel history accepted proof other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution).toHOL =
      (predicateDomain history accepted proof other
        (instanceAssignment history accepted proof other assignment substitution)).Carrier := by
  rw [UniformTypeDefinitionFamily.carrierModel, priorModel_carrier, ← evaluate_toHOL]
  apply congrArg Domain.Carrier
  rw [SourceTypeDefinitionTransport.sourceCarrierType, evaluate_op,
    primitiveFamilies_extend other _ _ (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2,
    extend_new]
  have arguments :
      (request.typeVariables.map fun name => substitution.apply (.var name)).map
        (evaluate (extend (primitiveFamilies other) (SourceTypeDefinitionTransport.operator request)
          (family history accepted proof other)) assignment) =
        instanceArguments history accepted proof other assignment substitution := by
    rw [instanceArguments, List.map_map]
    apply List.map_congr_left
    intro parameter _
    change _ = evaluate (primitiveFamilies (operators history accepted proof other)) assignment
      (substitution.apply (.var parameter))
    rw [operators, primitiveFamilies_extend other _ _
      (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2]
    rfl
  rw [arguments]
  exact family_valid history accepted proof other _ (List.length_map _)

noncomputable def abstractionInstance (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel history accepted proof other assignment).Carrier
      (Ty.function (substitution.apply result.core.witness.ty)
        (SourceTypeDefinitionTransport.sourceCarrierType request substitution)).toHOL :=
  cast (congrArg (HOL.Ty.denote.{0, w + 1} (carrierModel history accepted proof other assignment).Carrier)
    (Ty.toHOL_function _ _).symm)
    ((Equiv.cast (represented_carrier history accepted proof other assignment substitution)).symm.arrowCongr
      (Equiv.cast (new_carrier history accepted proof other assignment substitution)).symm
      (abstraction history accepted proof other
        (instanceAssignment history accepted proof other assignment substitution)))

noncomputable def representationInstance (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel history accepted proof other assignment).Carrier
      (Ty.function (SourceTypeDefinitionTransport.sourceCarrierType request substitution)
        (substitution.apply result.core.witness.ty)).toHOL :=
  cast (congrArg (HOL.Ty.denote.{0, w + 1} (carrierModel history accepted proof other assignment).Carrier)
    (Ty.toHOL_function _ _).symm)
    ((Equiv.cast (new_carrier history accepted proof other assignment substitution)).symm.arrowCongr
      (Equiv.cast (represented_carrier history accepted proof other assignment substitution)).symm
      (representation history accepted proof other
        (instanceAssignment history accepted proof other assignment substitution)))

def abstractionAnnotation (substitution : TypeSubst) : Ty :=
  Ty.function (substitution.apply result.core.witness.ty)
    (SourceTypeDefinitionTransport.sourceCarrierType request substitution)

def representationAnnotation (substitution : TypeSubst) : Ty :=
  Ty.function (SourceTypeDefinitionTransport.sourceCarrierType request substitution)
    (substitution.apply result.core.witness.ty)

private theorem arrowCast_heq {A B C D : Type (w + 1)} (domain : A = B) (codomain : C = D)
    (function : B → D) :
    HEq ((Equiv.cast domain).symm.arrowCongr (Equiv.cast codomain).symm function) function := by
  cases domain
  cases codomain
  rfl

theorem abstractionInstance_heq (substitution : TypeSubst) :
    HEq (abstractionInstance history accepted proof other assignment substitution)
      (abstraction history accepted proof other
        (instanceAssignment history accepted proof other assignment substitution)) := by
  unfold abstractionInstance
  exact (cast_heq _ _).trans (arrowCast_heq
    (represented_carrier history accepted proof other assignment substitution)
    (new_carrier history accepted proof other assignment substitution) _) 

theorem representationInstance_heq (substitution : TypeSubst) :
    HEq (representationInstance history accepted proof other assignment substitution)
      (representation history accepted proof other
        (instanceAssignment history accepted proof other assignment substitution)) := by
  unfold representationInstance
  exact (cast_heq _ _).trans (arrowCast_heq
    (new_carrier history accepted proof other assignment substitution)
    (represented_carrier history accepted proof other assignment substitution) _)

theorem instanceArguments_eq {first second : TypeSubst}
    (same : SourceTypeDefinitionTransport.sourceCarrierType request first =
      SourceTypeDefinitionTransport.sourceCarrierType request second) :
    instanceArguments history accepted proof other assignment first =
      instanceArguments history accepted proof other assignment second := by
  have arguments := (Ty.op.inj same).2
  change request.typeVariables.map (fun parameter => evaluate _ assignment (first.apply (.var parameter))) =
    request.typeVariables.map (fun parameter => evaluate _ assignment (second.apply (.var parameter)))
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map (evaluate
    (primitiveFamilies (operators history accepted proof other)) assignment)) arguments

/-- Equal public annotations force the same full semantic parameter tuple.
The arbitrary source witness used to recognize an instance cannot change
the actual abstraction value. -/
theorem abstractionInstance_choice_independent {first second : TypeSubst}
    (same : abstractionAnnotation (request := request) (result := result) first =
      abstractionAnnotation (request := request) (result := result) second) :
    HEq (abstractionInstance history accepted proof other assignment first)
      (abstractionInstance history accepted proof other assignment second) := by
  have carriers := congrArg (fun type => type.destFunction?.map Prod.snd) same
  simp only [abstractionAnnotation, Ty.destFunction?_function, Option.map_some] at carriers
  have arguments := instanceArguments_eq history accepted proof other assignment (Option.some.inj carriers)
  have canonical : HEq
      (abstraction history accepted proof other (instanceAssignment history accepted proof other assignment first))
      (abstraction history accepted proof other (instanceAssignment history accepted proof other assignment second)) := by
    unfold instanceAssignment
    rw [arguments]
  exact (abstractionInstance_heq history accepted proof other assignment first).trans
    (canonical.trans (abstractionInstance_heq history accepted proof other assignment second).symm)

theorem representationInstance_choice_independent {first second : TypeSubst}
    (same : representationAnnotation (request := request) (result := result) first =
      representationAnnotation (request := request) (result := result) second) :
    HEq (representationInstance history accepted proof other assignment first)
      (representationInstance history accepted proof other assignment second) := by
  have carriers := congrArg (fun type => type.destFunction?.map Prod.fst) same
  simp only [representationAnnotation, Ty.destFunction?_function, Option.map_some] at carriers
  have arguments := instanceArguments_eq history accepted proof other assignment (Option.some.inj carriers)
  have canonical : HEq
      (representation history accepted proof other (instanceAssignment history accepted proof other assignment first))
      (representation history accepted proof other (instanceAssignment history accepted proof other assignment second)) := by
    unfold instanceAssignment
    rw [arguments]
  exact (representationInstance_heq history accepted proof other assignment first).trans
    (canonical.trans (representationInstance_heq history accepted proof other assignment second).symm)

/-- All actual original public instances receive their constructed maps in
one source model. Unlicensed annotations retain ordinary inhabited model
data; this interpretation does not declare them admitted. -/
noncomputable def meanings : ∀ {type}, Symbol type →
    HOL.Ty.denote.{0, w + 1} (carrierModel history accepted proof other assignment).Carrier type
  | _, .variable sourceVar typed => (carrierModel history accepted proof other assignment).constDen (.variable sourceVar typed)
  | type, .constant constant annotation typed => by
      classical
      exact if named : constant = result.output.abstractionConstant then
        if declared : ∃ substitution : TypeSubst,
            annotation = abstractionAnnotation (request := request) (result := result) substitution then
          have sourceType : (abstractionAnnotation (request := request) (result := result) declared.choose).toHOL = type :=
            (congrArg Ty.toHOL declared.choose_spec).symm.trans typed
          sourceType ▸ abstractionInstance history accepted proof other assignment declared.choose
        else (carrierModel history accepted proof other assignment).constDen (.constant constant annotation typed)
      else if named : constant = result.output.representationConstant then
        if declared : ∃ substitution : TypeSubst,
            annotation = representationAnnotation (request := request) (result := result) substitution then
          have sourceType : (representationAnnotation (request := request) (result := result) declared.choose).toHOL = type :=
            (congrArg Ty.toHOL declared.choose_spec).symm.trans typed
          sourceType ▸ representationInstance history accepted proof other assignment declared.choose
        else (carrierModel history accepted proof other assignment).constDen (.constant constant annotation typed)
      else (carrierModel history accepted proof other assignment).constDen (.constant constant annotation typed)

noncomputable def model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard (carrierModel history accepted proof other assignment).Carrier
    (meanings history accepted proof other assignment)

theorem model_carrier : (model history accepted proof other assignment).Carrier =
    (carrierModel history accepted proof other assignment).Carrier := rfl

theorem model_fullDomains : (model history accepted proof other assignment).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem meanings_abstraction (substitution : TypeSubst) :
    (model history accepted proof other assignment).constDen
      (.constant result.output.abstractionConstant
        (abstractionAnnotation (request := request) (result := result) substitution) rfl) =
      abstractionInstance history accepted proof other assignment substitution := by
  classical
  have existsInstance : ∃ source : TypeSubst,
      abstractionAnnotation (request := request) (result := result) substitution =
        abstractionAnnotation (request := request) (result := result) source := ⟨substitution, rfl⟩
  simp only [model, HOL.HenkinModel.standard]
  simp only [meanings, dif_pos existsInstance]
  apply eq_of_heq
  exact (eqRec_heq _ _).trans
    (abstractionInstance_choice_independent history accepted proof other assignment existsInstance.choose_spec.symm)

theorem meanings_representation (substitution : TypeSubst) :
    (model history accepted proof other assignment).constDen
      (.constant result.output.representationConstant
        (representationAnnotation (request := request) (result := result) substitution) rfl) =
      representationInstance history accepted proof other assignment substitution := by
  classical
  have existsInstance : ∃ source : TypeSubst,
      representationAnnotation (request := request) (result := result) substitution =
        representationAnnotation (request := request) (result := result) source := ⟨substitution, rfl⟩
  simp only [model, HOL.HenkinModel.standard]
  simp only [meanings, dif_neg (SourceTypeDefinitionTransport.admitted_constants_distinct accepted),
    dif_pos existsInstance]
  apply eq_of_heq
  exact (eqRec_heq _ _).trans
    (representationInstance_choice_independent history accepted proof other assignment existsInstance.choose_spec.symm)

theorem meanings_other {constant : Const} {annotation : Ty} {type : HOL.Ty AtomicTy}
    (typed : annotation.toHOL = type)
    (notAbstraction : constant ≠ result.output.abstractionConstant)
    (notRepresentation : constant ≠ result.output.representationConstant) :
    (model history accepted proof other assignment).constDen (.constant constant annotation typed) =
      (carrierModel history accepted proof other assignment).constDen (.constant constant annotation typed) := by
  classical
  simp only [model, HOL.HenkinModel.standard, meanings, dif_neg notAbstraction, dif_neg notRepresentation]

theorem meanings_variable (sourceVar : SourceVar) {type : HOL.Ty AtomicTy}
    (typed : sourceVar.ty.toHOL = type) :
    (model history accepted proof other assignment).constDen (.variable sourceVar typed) =
      (carrierModel history accepted proof other assignment).constDen (.variable sourceVar typed) := by
  simp only [model, HOL.HenkinModel.standard, meanings]

include accepted in
/-- Both new provenance-bearing identities are absent from the entire old
constant table, as earned by the original admission. -/
theorem new_constants_unregistered :
    context.signature.constants result.output.abstractionConstant = none ∧
      context.signature.constants result.output.representationConstant = none := by
  constructor
  · apply context.constant_unregistered
    rw [(admitSourceTypeInTheory_pointwise accepted).2.1]
    exact (SourceTypeDefinitionTransport.admitted_names_fresh accepted).2.1
  · apply context.constant_unregistered
    rw [(admitSourceTypeInTheory_pointwise accepted).2.2.1]
    exact (SourceTypeDefinitionTransport.admitted_names_fresh accepted).2.2.1

include accepted in
theorem licensed_old_constant {constant : Const} {annotation : Ty}
    (declared : ConstantInstance context.signature constant annotation) :
    constant ≠ result.output.abstractionConstant ∧ constant ≠ result.output.representationConstant := by
  obtain ⟨schema, substitution, registered, instanceEq⟩ := declared
  constructor
  · intro same
    rw [same, (new_constants_unregistered accepted).1] at registered
    cases registered
  · intro same
    rw [same, (new_constants_unregistered accepted).2] at registered
    cases registered

theorem model_carrierModel_agreement :
    SourceAgreement context.signature (model history accepted proof other assignment)
      (carrierModel history accepted proof other assignment) where
  carriers := fun _ _ => rfl
  constants := by
    intro constant annotation type typed formed declared
    have different := licensed_old_constant accepted declared
    exact heq_of_eq (meanings_other history accepted proof other assignment typed different.1 different.2)
  variableValues := by
    intro sourceVar type typed formed
    exact heq_of_eq (meanings_variable history accepted proof other assignment sourceVar typed)

theorem model_old_agreement
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2) :
    SourceAgreement context.signature (model history accepted proof other assignment)
      (priorModel history other assignment) :=
  ConstantHistoryInstanceCoherence.sourceAgreement_trans
    (model_carrierModel_agreement history accepted proof other assignment)
    (carrierModel_old_agreement history accepted proof other assignment functionArity)

theorem model_models_old
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed context.signature term) :
    (model history accepted proof other assignment).models formula ↔
      (priorModel history other assignment).models formula :=
  (model_old_agreement history accepted proof other assignment functionArity).models
    (history.includes.1 TypeOp.function 2 functionArity)
    (model_fullDomains history accepted proof other assignment)
    (priorModel_fullDomains history other assignment) translated formed

private theorem apply_heq {A A' B B' : Type (w + 1)}
    (domain : A = A') (codomain : B = B') {function : A → B} {otherFunction : A' → B'}
    {argument : A} {otherArgument : A'} (functions : HEq function otherFunction)
    (arguments : HEq argument otherArgument) : HEq (function argument) (otherFunction otherArgument) := by
  cases domain
  cases codomain
  exact heq_of_eq (congrArg₂ (fun f x => f x) (eq_of_heq functions) (eq_of_heq arguments))

theorem meanings_abstraction_heq (substitution : TypeSubst) {type : HOL.Ty AtomicTy}
    (typed : (abstractionAnnotation (request := request) (result := result) substitution).toHOL = type) :
    HEq ((model history accepted proof other assignment).constDen
      (.constant result.output.abstractionConstant
        (abstractionAnnotation (request := request) (result := result) substitution) typed))
      (abstraction history accepted proof other
        (instanceAssignment history accepted proof other assignment substitution)) := by
  cases typed
  exact (heq_of_eq (meanings_abstraction history accepted proof other assignment substitution)).trans
    (abstractionInstance_heq history accepted proof other assignment substitution)

theorem meanings_representation_heq (substitution : TypeSubst) {type : HOL.Ty AtomicTy}
    (typed : (representationAnnotation (request := request) (result := result) substitution).toHOL = type) :
    HEq ((model history accepted proof other assignment).constDen
      (.constant result.output.representationConstant
        (representationAnnotation (request := request) (result := result) substitution) typed))
      (representation history accepted proof other
        (instanceAssignment history accepted proof other assignment substitution)) := by
  cases typed
  exact (heq_of_eq (meanings_representation history accepted proof other assignment substitution)).trans
    (representationInstance_heq history accepted proof other assignment substitution)

theorem model_abstraction_representation (substitution : TypeSubst)
    (value : HOL.Ty.denote.{0, w + 1} (model history accepted proof other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution).toHOL) :
    (model history accepted proof other assignment).constDen
        (.constant result.output.abstractionConstant
          (abstractionAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _))
      ((model history accepted proof other assignment).constDen
        (.constant result.output.representationConstant
          (representationAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _)) value) = value := by
  have reps := apply_heq
    (new_carrier history accepted proof other assignment substitution)
    (represented_carrier history accepted proof other assignment substitution)
    (meanings_representation_heq history accepted proof other assignment substitution (Ty.toHOL_function _ _))
    (cast_heq (new_carrier history accepted proof other assignment substitution) value).symm
  have abstractions := apply_heq
    (represented_carrier history accepted proof other assignment substitution)
    (new_carrier history accepted proof other assignment substitution)
    (meanings_abstraction_heq history accepted proof other assignment substitution (Ty.toHOL_function _ _)) reps
  rw [abstraction_representation] at abstractions
  exact eq_of_heq (abstractions.trans (cast_heq (new_carrier history accepted proof other assignment substitution) value))

/-- The comparison uses the actual admitted successor type table and the
unchanged predecessor constant table. Thus original constants may be used
at newly formed carrier instances without becoming new declarations. -/
def comparisonSignature : Signature :=
  { context.signature with typeOperators := result.context.signature.typeOperators }

include accepted in
theorem comparisonSignature_includes :
    context.signature.Includes (comparisonSignature (context := context) (result := result)) := by
  exact ⟨(admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.2.2.1.1,
    fun _ _ registered => registered⟩

theorem model_comparison_agreement :
    SourceAgreement (comparisonSignature (context := context) (result := result))
      (model history accepted proof other assignment) (carrierModel history accepted proof other assignment) where
  carriers := fun _ _ => rfl
  constants := by
    intro constant annotation type typed formed declared
    have oldDeclaration : ConstantInstance context.signature constant annotation := declared
    have different := licensed_old_constant accepted oldDeclaration
    exact heq_of_eq (meanings_other history accepted proof other assignment typed different.1 different.2)
  variableValues := by
    intro sourceVar type typed formed
    exact heq_of_eq (meanings_variable history accepted proof other assignment sourceVar typed)

include accepted in
theorem instance_predicate_formed (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    AnnotationsFormed (comparisonSignature (context := context) (result := result))
      (SourceTypeDefinitionTransport.instanceTerm substitution result.core.predicate).term := by
  apply annotations_instance_formed_supported _ substitution
    (((admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1).mono
      (comparisonSignature_includes accepted))
  intro parameter occurs
  have member := List.mem_toFinset.mp
    ((admitted_parameter_guards accepted).2.1.symm ▸ occurs)
  simp only [SourceTypeDefinitionTransport.sourceCarrierType, TypeFormed] at formedCarrier
  have child := formedCarrier.2 (substitution.apply (.var parameter)) (List.mem_map.mpr ⟨parameter, member, rfl⟩)
  exact (typeFormed_eq_of_operators result.context.signature
    (comparisonSignature (context := context) (result := result)) rfl _).mp child

theorem model_instance_predicate_same (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    (model history accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v) =
    (carrierModel history accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v) := by
  apply eq_of_heq
  apply (model_comparison_agreement history accepted proof other assignment).denote
    ((comparisonSignature_includes accepted).1 TypeOp.function 2
      (SourceTypeDefinitionTransport.admitted_function_arity accepted))
    (model_fullDomains history accepted proof other assignment)
    (priorModel_fullDomains history _ assignment)
    (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTranslated
    (instance_predicate_formed accepted substitution formedCarrier)
  · intro type member
    cases member
  · intro type index
    nomatch index

private theorem denote_reduct_heq (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (substitution : TypeSubst) {type : HOL.Ty AtomicTy}
    (term : HOL.ClosedTerm Symbol type) :
    HEq ((reindexedModel substitution M).denote term (fun v => nomatch v))
      (M.denote (HOL.mapTypes substitution.baseInstance substitution.symbolInstance term) (fun v => nomatch v)) := by
  let valuation : M.Valuation ([].map (HOL.Ty.substitute substitution.baseInstance)) := fun v => nomatch v
  have preserved := HOL.HenkinModel.denote_mapTypes substitution.baseInstance substitution.symbolInstance M full term valuation
  have normalized := HOL.HenkinModel.denote_closed_valuation_eq (reindexedModel substitution M) term
    (fun v => nomatch v) (HOL.HenkinModel.typeReductValuation substitution.baseInstance substitution.symbolInstance M valuation)
  change HOL.Ty.denoteSubstituteEquiv substitution.baseInstance M.Carrier _
    ((reindexedModel substitution M).denote term
      (HOL.HenkinModel.typeReductValuation substitution.baseInstance substitution.symbolInstance M valuation)) = _ at preserved
  rw [← normalized] at preserved
  exact (HOL.Ty.denoteSubstituteEquiv_apply_heq _ _ _ _).symm.trans (heq_of_eq preserved)

private theorem compose_closed {A B : Type (w + 1)} {first : A} {second : B}
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) {type : HOL.Ty AtomicTy}
    (term : HOL.ClosedTerm Symbol type) (firstValuation secondValuation : M.Valuation [])
    (left : HEq first (M.denote term firstValuation))
    (right : HEq (M.denote term secondValuation) second) : HEq first second :=
  left.trans ((heq_of_eq (M.denote_closed_valuation_eq term firstValuation secondValuation)).trans right)

set_option backward.isDefEq.respectTransparency false in
theorem carrierModel_instance_predicate_heq
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (substitution : TypeSubst) :
    HEq ((carrierModel history accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v))
      ((priorModel history other (instanceAssignment history accepted proof other assignment substitution)).denote
        (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v)) := by
  let next := operators history accepted proof other
  let changed := reindex (primitiveFamilies next) substitution assignment
  have originalAnnotations := (admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1
  have historyAgreement := ConstantHistoryInstanceCoherence.constantHistory_instance_agreement_optional_selection
    history functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration next assignment substitution
  have values := historyAgreement.denote
    (history.includes.1 TypeOp.function 2 functionArity)
    (priorModel_fullDomains history next changed)
    (reindexedModel_fullDomains substitution (priorModel history next assignment))
    (TypeAdmission.admittedImage accepted).predicateTranslated originalAnnotations
    (by intro type member; cases member) (fun v => nomatch v) (fun v => nomatch v)
    (by intro type index; nomatch index)
  have normalizedValues : HEq
      ((priorModel history next changed).denote (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v))
      ((reindexedModel substitution (priorModel history next assignment)).denote
        (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v)) :=
    (heq_of_eq ((priorModel history next changed).denote_closed_valuation_eq _ _ _)).trans
      (values.trans (heq_of_eq ((reindexedModel substitution
        (priorModel history next assignment)).denote_closed_valuation_eq _ _ _)))
  have mapped := denote_reduct_heq (priorModel history next assignment)
    (priorModel_fullDomains history next assignment) substitution (TypeAdmission.admittedImage accepted).predicateTerm
  have translated := ConstantHistoryInstanceCoherence.translation_type_instance context.signature equalityParameter
    (history.includes.2 Const.equality _ equalityRegistered) substitution
    (TypeAdmission.admittedImage accepted).predicateTranslated originalAnnotations
  have same := translated.unique (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTranslated
  have mappedActual := ConstantHistoryInstanceCoherence.denote_closed_heq (priorModel history next assignment)
    same.1 same.2 (fun v => nomatch v) (fun v => nomatch v)
  have oldOperators := constantHistory_operator_agreement history functionArity other
    (SourceTypeDefinitionTransport.operator request) (family history accepted proof other)
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted) changed
  have unchanged := oldOperators.denote
    (history.includes.1 TypeOp.function 2 functionArity)
    (priorModel_fullDomains history next changed) (priorModel_fullDomains history other changed)
    (TypeAdmission.admittedImage accepted).predicateTranslated originalAnnotations
    (by intro type member; cases member) (fun v => nomatch v) (fun v => nomatch v)
    (by intro type index; nomatch index)
  have parameters := ModelAssignmentSupport.denote_parameter_agreement other (priorModel history other)
    (priorModel_carrier history other) (priorModel_fullDomains history other) (history_initial_symbol_local history other)
    changed (instanceAssignment history accepted proof other assignment substitution)
    (TypeAdmission.admittedImage accepted).predicateTranslated
    (by
      intro parameter occurs
      exact (instanceAssignment_agrees history accepted proof other assignment substitution parameter
        (List.mem_toFinset.mp ((admitted_parameter_guards accepted).2.1.symm ▸ occurs))).symm)
    (by intro parameter occurs; simp [ModelAssignmentSupport.contextSupport, Ty.typeVariablesList] at occurs)
    (fun v => nomatch v) (fun v => nomatch v) (by intro type index; nomatch index)
  have normalized : HEq
      ((priorModel history other changed).denote (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v))
      ((priorModel history other (instanceAssignment history accepted proof other assignment substitution)).denote
        (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v)) :=
    (heq_of_eq ((priorModel history other changed).denote_closed_valuation_eq _ _ _)).trans
    (parameters.trans (heq_of_eq ((priorModel history other
      (instanceAssignment history accepted proof other assignment substitution)).denote_closed_valuation_eq _ _ _)))
  have instanceValues := compose_closed (priorModel history next assignment)
    (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (TypeAdmission.admittedImage accepted).predicateTerm)
    _ _ mappedActual.symm (mapped.symm.trans normalizedValues.symm)

  exact instanceValues.trans (unchanged.trans normalized)

private theorem equality_heq {A A' : Type (w + 1)} (carrier : A = A')
    {left right : A} {otherLeft otherRight : A'}
    (lefts : HEq left otherLeft) (rights : HEq right otherRight) :
    (left = right) ↔ (otherLeft = otherRight) := by
  cases carrier
  rw [eq_of_heq lefts, eq_of_heq rights]

private theorem eqv_iff_eq (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (type : HOL.Ty AtomicTy)
    (left right : HOL.Ty.denote.{0, w + 1} M.Carrier type) :
    M.Eqv type left right ↔ left = right := by
  constructor
  · exact M.eq_of_eqv_of_fullDomains full
  · intro equal
    subst right
    exact M.eqv_refl (full type left)

section Equations

variable (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
  (equalityParameter : Name)
  (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
  (selectionParameter : Name)
  (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
    initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))

include functionArity equalityRegistered selectionDeclaration in
theorem model_instance_predicate (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution))
    (value : HOL.Ty.denote.{0, w + 1} (model history accepted proof other assignment).Carrier
      (substitution.apply result.core.witness.ty).toHOL) :
    (((model history accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v)) value).down =
    TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
      (priorModel history other (instanceAssignment history accepted proof other assignment substitution))
      (cast (represented_carrier history accepted proof other assignment substitution) value) := by
  have functions := compose_closed (carrierModel history accepted proof other assignment)
    (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm _ _
    (heq_of_eq (model_instance_predicate_same history accepted proof other assignment substitution formedCarrier))
    (carrierModel_instance_predicate_heq history accepted proof other assignment
      functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration substitution)
  have arguments := (cast_heq (represented_carrier history accepted proof other assignment substitution) value).symm
  have outputs := apply_heq (represented_carrier history accepted proof other assignment substitution) rfl functions arguments
  apply Eq.trans (congrArg (fun truth : ULift.{w + 1, 0} Prop => truth.down) (eq_of_heq outputs))
  exact congrArg (fun function => (function
    (cast (represented_carrier history accepted proof other assignment substitution) value)).down)
    ((priorModel history other (instanceAssignment history accepted proof other assignment substitution)).denote_closed_valuation_eq
      (TypeAdmission.admittedImage accepted).predicateTerm _ _)

include functionArity equalityRegistered selectionDeclaration in
theorem model_predicate_iff_representation_abstraction (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution))
    (value : HOL.Ty.denote.{0, w + 1} (model history accepted proof other assignment).Carrier
      (substitution.apply result.core.witness.ty).toHOL) :
    (((model history accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v)) value).down ↔
      (model history accepted proof other assignment).constDen
          (.constant result.output.representationConstant
            (representationAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _))
        ((model history accepted proof other assignment).constDen
          (.constant result.output.abstractionConstant
            (abstractionAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _)) value) = value := by
  rw [model_instance_predicate history accepted proof other assignment functionArity equalityParameter equalityRegistered
    selectionParameter selectionDeclaration substitution formedCarrier value]
  have abstractions := apply_heq
    (represented_carrier history accepted proof other assignment substitution)
    (new_carrier history accepted proof other assignment substitution)
    (meanings_abstraction_heq history accepted proof other assignment substitution (Ty.toHOL_function _ _))
    (cast_heq (represented_carrier history accepted proof other assignment substitution) value).symm
  have reps := apply_heq
    (new_carrier history accepted proof other assignment substitution)
    (represented_carrier history accepted proof other assignment substitution)
    (meanings_representation_heq history accepted proof other assignment substitution (Ty.toHOL_function _ _)) abstractions
  exact (predicate_iff_representation_abstraction history accepted proof other
    (instanceAssignment history accepted proof other assignment substitution) _).trans
    (equality_heq (represented_carrier history accepted proof other assignment substitution) reps
      (cast_heq (represented_carrier history accepted proof other assignment substitution) value).symm).symm

set_option backward.isDefEq.respectTransparency false in
theorem model_models_abstractionRepresentation (substitution : TypeSubst) :
    (model history accepted proof other assignment).models
      (SourceTypeDefinitionTransport.abstractionRepresentationFormula (request := request) (result := result) substitution) := by
  change (model history accepted proof other assignment).Eqv _ _ _
  apply (eqv_iff_eq _ (model_fullDomains history accepted proof other assignment) _ _ _).mpr
  exact model_abstraction_representation history accepted proof other assignment substitution _

include functionArity equalityRegistered selectionDeclaration in
set_option backward.isDefEq.respectTransparency false in
theorem model_models_representationAbstraction (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    (model history accepted proof other assignment).models
      (SourceTypeDefinitionTransport.representationAbstractionFormula accepted substitution) := by
  let value := (model history accepted proof other assignment).constDen
    (.variable ⟨Name.global "r", (SourceTypeDefinitionTransport.instanceTerm substitution result.core.witness).ty⟩ rfl)
  have meaning : (((model history accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v)) value).down ↔
      (model history accepted proof other assignment).Eqv
        (SourceTypeDefinitionTransport.instanceTerm substitution result.core.witness).ty.toHOL
        ((model history accepted proof other assignment).constDen
          (.constant result.output.representationConstant
            (representationAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _))
          ((model history accepted proof other assignment).constDen
            (.constant result.output.abstractionConstant
              (abstractionAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _)) value)) value :=
    (model_predicate_iff_representation_abstraction history accepted proof other assignment
      functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration substitution formedCarrier value).trans
      (eqv_iff_eq _ (model_fullDomains history accepted proof other assignment) _ _ _).symm
  convert meaning using 1
  simp only [SourceTypeDefinitionTransport.representationAbstractionFormula,
    SourceTypeDefinitionTransport.abstractionTerm, SourceTypeDefinitionTransport.representationTerm,
    abstractionAnnotation, representationAnnotation, equalityLambda, HOL.HenkinModel.models,
    HOL.PreModel.models, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend, HOL.PreModel.Eqv, value]
  apply iff_congr
  · exact iff_of_eq (congrArg (fun function => (function value).down)
      ((model history accepted proof other assignment).denote_closed_valuation_eq
        (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm _ _))
  · rfl

include functionArity equalityRegistered selectionDeclaration in
/-- Every admitted instance of both original retained equations is true in
one uniform source model. The only additional conditions are the actual
primitive declaration licences and formation of the public new carrier. -/
theorem model_models_retained_equations (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution))
    {first second : HOL.ClosedFormula Symbol}
    (firstTranslation : TranslatesCompositionally []
      (SourceTypeDefinitionTransport.instanceTerm substitution result.output.abstractionRepresentationTheorem.sequent.concl).term
      .prop first)
    (secondTranslation : TranslatesCompositionally []
      (SourceTypeDefinitionTransport.instanceTerm substitution result.output.representationAbstractionTheorem.sequent.concl).term
      .prop second) :
    (model history accepted proof other assignment).models first ∧
      (model history accepted proof other assignment).models second := by
  rw [← (SourceTypeDefinitionTransport.abstractionRepresentation_translated accepted substitution).unique_eq firstTranslation,
    ← (SourceTypeDefinitionTransport.representationAbstraction_translated accepted substitution).unique_eq secondTranslation]
  exact ⟨model_models_abstractionRepresentation history accepted proof other assignment substitution,
    model_models_representationAbstraction history accepted proof other assignment functionArity equalityParameter
      equalityRegistered selectionParameter selectionDeclaration substitution formedCarrier⟩

include functionArity equalityRegistered selectionDeclaration in
/-- Formation of the original public abstraction annotation earns the
carrier-formation condition of the all-instance retained-equation law. -/
theorem model_models_retained_of_public_abstraction (substitution : TypeSubst)
    (publicFormed : TypeFormed result.context.signature
      (abstractionAnnotation (request := request) (result := result) substitution))
    {first second : HOL.ClosedFormula Symbol}
    (firstTranslation : TranslatesCompositionally []
      (SourceTypeDefinitionTransport.instanceTerm substitution result.output.abstractionRepresentationTheorem.sequent.concl).term
      .prop first)
    (secondTranslation : TranslatesCompositionally []
      (SourceTypeDefinitionTransport.instanceTerm substitution result.output.representationAbstractionTheorem.sequent.concl).term
      .prop second) :
    (model history accepted proof other assignment).models first ∧
      (model history accepted proof other assignment).models second :=
  model_models_retained_equations history accepted proof other assignment functionArity equalityParameter
    equalityRegistered selectionParameter selectionDeclaration substitution
    (publicFormed.function_components _).2 firstTranslation secondTranslation

end Equations

namespace Controls

open UniformTypeDefinitionFamily.Controls DefinitionAdapters.ContextControls

def booleanInstance : TypeSubst := ⟨[(TypeFamilySemantics.Controls.alpha, Ty.bool)]⟩

def functionInstance : TypeSubst :=
  ⟨[(TypeFamilySemantics.Controls.alpha, Ty.function Ty.bool Ty.bool)]⟩

/-- The parameter itself may be the newly declared type at a previous
parameter instance. This remains one finite original source type. -/
def nestedInstance : TypeSubst :=
  ⟨[(TypeFamilySemantics.Controls.alpha,
    SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest booleanInstance)]⟩

def malformedInstance : TypeSubst :=
  ⟨[(TypeFamilySemantics.Controls.alpha, .op TypeOp.function [])]⟩

theorem boolean_carrier_formed : TypeFormed polymorphicResult.context.signature
    (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest booleanInstance) := by
  apply (typeFormedB_eq_true_iff _ _).mp
  decide +kernel

theorem function_carrier_formed : TypeFormed polymorphicResult.context.signature
    (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest functionInstance) := by
  apply (typeFormedB_eq_true_iff _ _).mp
  decide +kernel

theorem nested_carrier_formed : TypeFormed polymorphicResult.context.signature
    (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest nestedInstance) := by
  apply (typeFormedB_eq_true_iff _ _).mp
  decide +kernel

theorem malformed_carrier_refused : typeFormedB polymorphicResult.context.signature
    (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest malformedInstance) = false := by
  decide +kernel

theorem malformed_public_annotation_refused :
    constantInstanceB polymorphicResult.context.signature certificates polymorphicResult.output.abstractionConstant Ty.bool = false := by
  decide +kernel

theorem public_boolean_instance_registered :
    constantInstanceB polymorphicResult.context.signature (fun _ _ => booleanInstance)
      polymorphicResult.output.abstractionConstant
      (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) booleanInstance) = true := by
  decide +kernel

theorem public_nested_instance_registered :
    constantInstanceB polymorphicResult.context.signature (fun _ _ => nestedInstance)
      polymorphicResult.output.abstractionConstant
      (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) nestedInstance) = true := by
  decide +kernel

/-- One actual model simultaneously validates the original equation
instances at Boolean, function and nested newly declared types. -/
theorem three_instances_one_model (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let uniform := model DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other assignment
    ∀ substitution ∈ [booleanInstance, functionInstance, nestedInstance],
      uniform.models (SourceTypeDefinitionTransport.abstractionRepresentationFormula
        (request := polymorphicRequest) (result := polymorphicResult) substitution) ∧
      uniform.models (SourceTypeDefinitionTransport.representationAbstractionFormula polymorphic_result_admitted substitution) := by
  intro uniform substitution member
  have formed : TypeFormed polymorphicResult.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest substitution) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact boolean_carrier_formed
    · exact function_carrier_formed
    · exact nested_carrier_formed
  exact ⟨model_models_abstractionRepresentation DefinitionHistoryModels.Controls.polymorphicDefinitions
    polymorphic_result_admitted polymorphic_existence_proven other assignment substitution,
    model_models_representationAbstraction DefinitionHistoryModels.Controls.polymorphicDefinitions
      polymorphic_result_admitted polymorphic_existence_proven other assignment
      (core_includes.1 TypeOp.function 2 function_registered) equalityParameter
      ConstantHistoryInstanceCoherence.Controls.core_equality_registered equalityParameter
      (Or.inl ConstantHistoryInstanceCoherence.Controls.core_selection_unregistered) substitution formed⟩

theorem original_alias_preserved (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    HEq ((model DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other assignment).constDen
      (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
        DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty rfl))
      ((priorModel DefinitionHistoryModels.Controls.polymorphicDefinitions other assignment).constDen
        (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
          DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty rfl)) :=
  (model_old_agreement DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
    polymorphic_existence_proven other assignment (core_includes.1 TypeOp.function 2 function_registered)).constants _ _ rfl
    ConstantHistoryInstanceCoherence.Controls.polymorphic_alias_type_formed
    ConstantHistoryInstanceCoherence.Controls.polymorphic_alias_instance_registered

theorem original_redeclaration_refused :
    admitSourceTypeInTheory polymorphicResult.context polymorphicCertificates polymorphicRequest = none :=
  SourceTypeDefinitionTransport.repeated_source_definition_refused polymorphic_result_admitted polymorphicCertificates

end Controls

end Mettapedia.Languages.HOLLight.UniformTypeDefinitionModels
