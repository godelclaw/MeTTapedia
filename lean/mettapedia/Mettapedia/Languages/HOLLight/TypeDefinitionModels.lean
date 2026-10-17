import Mettapedia.Languages.HOLLight.DefinitionModelFamily

/-!
# Installed original source symbols over a constructed mixed predecessor

The next witnessed family and original abstraction/representation Symbols
are interpreted over the actual preceding model construction. Source
annotations are the original admitted declarations; no new syntax or
acceptance authority is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.TypeDefinitionModels

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters DefinitionModelFamily
open DefinitionModelFamily.Witnessed
open UniformTypeDefinitionFamily (tupleAssignment tupleAssignment_mapped represented_support)
open UniformTypeDefinitionModels (abstractionAnnotation representationAnnotation licensed_old_constant comparisonSignature comparisonSignature_includes instance_predicate_formed)
open UniformTypeDefinitionInstances (abstractionAnnotation_composition representationAnnotation_composition licensed_abstraction_instance licensed_representation_instance old_constant_instance)
open ConstantHistoryExpandedTypes (withTypes)

universe w

variable {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}
  (prior : Family.{w} initial context theory)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (theory) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

noncomputable def instanceArguments (substitution : TypeSubst) : List Domain.{w} :=
  request.typeVariables.map (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment)

noncomputable def instanceAssignment (substitution : TypeSubst) : Assignment.{w} :=
  tupleAssignment request.typeVariables (instanceArguments prior accepted proof other assignment substitution)

theorem instanceAssignment_agrees (substitution : TypeSubst) :
    ∀ parameter ∈ request.typeVariables,
      instanceAssignment prior accepted proof other assignment substitution parameter =
        reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment parameter :=
  tupleAssignment_mapped _ _

/-- Original admission and support earn the complete represented carrier
transport. Replacement types may themselves contain the new operator. -/
theorem represented_carrier (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (substitution.apply result.core.witness.ty).toHOL =
    HOL.Ty.denote.{0, w + 1}
      (prior.model other (instanceAssignment prior accepted proof other assignment substitution)).Carrier
      result.core.witness.ty.toHOL := by
  rw [Witnessed.carrierModel_carrier, prior.carrier,
    ← evaluate_toHOL, ← evaluate_toHOL]
  apply congrArg Domain.Carrier
  rw [evaluate_apply, operators]
  rw [domain_extend_formed context.signature (prior.operators other) _ _
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted) _ _
    (SourceTypeDefinitionTransport.admitted_represented_formed accepted)]
  apply evaluate_parameter_agreement
  intro parameter member
  exact (instanceAssignment_agrees prior accepted proof other assignment substitution parameter
    (List.mem_toFinset.mp (represented_support accepted member))).symm

theorem new_carrier (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution).toHOL =
      (predicateDomain prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)).Carrier := by
  rw [Witnessed.carrierModel_carrier, ← evaluate_toHOL]
  apply congrArg Domain.Carrier
  rw [SourceTypeDefinitionTransport.sourceCarrierType, evaluate_op, operators,
    primitiveFamilies_extend (prior.operators other) _ _ (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2,
    extend_new]
  have arguments :
      (request.typeVariables.map fun name => substitution.apply (.var name)).map
        (evaluate (extend (primitiveFamilies (prior.operators other)) (SourceTypeDefinitionTransport.operator request)
          (family prior accepted proof other)) assignment) =
        instanceArguments prior accepted proof other assignment substitution := by
    rw [instanceArguments, List.map_map]
    apply List.map_congr_left
    intro parameter _
    change _ = evaluate (primitiveFamilies (operators prior accepted proof other)) assignment
      (substitution.apply (.var parameter))
    rw [operators, primitiveFamilies_extend (prior.operators other) _ _
      (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2]
    rfl
  rw [arguments]
  exact family_valid prior accepted proof other _ (List.length_map _)

noncomputable def abstractionInstance (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (Ty.function (substitution.apply result.core.witness.ty)
        (SourceTypeDefinitionTransport.sourceCarrierType request substitution)).toHOL :=
  cast (congrArg (HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier)
    (Ty.toHOL_function _ _).symm)
    ((Equiv.cast (represented_carrier prior accepted proof other assignment substitution)).symm.arrowCongr
      (Equiv.cast (new_carrier prior accepted proof other assignment substitution)).symm
      (abstraction prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)))

noncomputable def representationInstance (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (Ty.function (SourceTypeDefinitionTransport.sourceCarrierType request substitution)
        (substitution.apply result.core.witness.ty)).toHOL :=
  cast (congrArg (HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier)
    (Ty.toHOL_function _ _).symm)
    ((Equiv.cast (new_carrier prior accepted proof other assignment substitution)).symm.arrowCongr
      (Equiv.cast (represented_carrier prior accepted proof other assignment substitution)).symm
      (representation prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)))

private theorem arrowCast_heq {A B C D : Type (w + 1)} (domain : A = B) (codomain : C = D)
    (function : B → D) :
    HEq ((Equiv.cast domain).symm.arrowCongr (Equiv.cast codomain).symm function) function := by
  cases domain
  cases codomain
  rfl

theorem abstractionInstance_heq (substitution : TypeSubst) :
    HEq (abstractionInstance prior accepted proof other assignment substitution)
      (abstraction prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)) := by
  unfold abstractionInstance
  exact (cast_heq _ _).trans (arrowCast_heq
    (represented_carrier prior accepted proof other assignment substitution)
    (new_carrier prior accepted proof other assignment substitution) _) 

theorem representationInstance_heq (substitution : TypeSubst) :
    HEq (representationInstance prior accepted proof other assignment substitution)
      (representation prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)) := by
  unfold representationInstance
  exact (cast_heq _ _).trans (arrowCast_heq
    (new_carrier prior accepted proof other assignment substitution)
    (represented_carrier prior accepted proof other assignment substitution) _)

theorem instanceArguments_eq {first second : TypeSubst}
    (same : SourceTypeDefinitionTransport.sourceCarrierType request first =
      SourceTypeDefinitionTransport.sourceCarrierType request second) :
    instanceArguments prior accepted proof other assignment first =
      instanceArguments prior accepted proof other assignment second := by
  have arguments := (Ty.op.inj same).2
  change request.typeVariables.map (fun parameter => evaluate _ assignment (first.apply (.var parameter))) =
    request.typeVariables.map (fun parameter => evaluate _ assignment (second.apply (.var parameter)))
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map (evaluate
    (primitiveFamilies (operators prior accepted proof other)) assignment)) arguments

/-- Equal public annotations force the same full semantic parameter tuple.
The arbitrary source witness used to recognize an instance cannot change
the actual abstraction value. -/
theorem abstractionInstance_choice_independent {first second : TypeSubst}
    (same : abstractionAnnotation (request := request) (result := result) first =
      abstractionAnnotation (request := request) (result := result) second) :
    HEq (abstractionInstance prior accepted proof other assignment first)
      (abstractionInstance prior accepted proof other assignment second) := by
  have carriers := congrArg (fun type => type.destFunction?.map Prod.snd) same
  simp only [abstractionAnnotation, Ty.destFunction?_function, Option.map_some] at carriers
  have arguments := instanceArguments_eq prior accepted proof other assignment (Option.some.inj carriers)
  have canonical : HEq
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other assignment first))
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other assignment second)) := by
    unfold instanceAssignment
    rw [arguments]
  exact (abstractionInstance_heq prior accepted proof other assignment first).trans
    (canonical.trans (abstractionInstance_heq prior accepted proof other assignment second).symm)

theorem representationInstance_choice_independent {first second : TypeSubst}
    (same : representationAnnotation (request := request) (result := result) first =
      representationAnnotation (request := request) (result := result) second) :
    HEq (representationInstance prior accepted proof other assignment first)
      (representationInstance prior accepted proof other assignment second) := by
  have carriers := congrArg (fun type => type.destFunction?.map Prod.fst) same
  simp only [representationAnnotation, Ty.destFunction?_function, Option.map_some] at carriers
  have arguments := instanceArguments_eq prior accepted proof other assignment (Option.some.inj carriers)
  have canonical : HEq
      (representation prior accepted proof other (instanceAssignment prior accepted proof other assignment first))
      (representation prior accepted proof other (instanceAssignment prior accepted proof other assignment second)) := by
    unfold instanceAssignment
    rw [arguments]
  exact (representationInstance_heq prior accepted proof other assignment first).trans
    (canonical.trans (representationInstance_heq prior accepted proof other assignment second).symm)

/-- All actual original public instances receive their constructed maps in
one source model. Unlicensed annotations retain ordinary inhabited model
data; this interpretation does not declare them admitted. -/
noncomputable def meanings : ∀ {type}, Symbol type →
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier type
  | _, .variable sourceVar typed => (carrierModel prior accepted proof other assignment).constDen (.variable sourceVar typed)
  | type, .constant constant annotation typed => by
      classical
      exact if named : constant = result.output.abstractionConstant then
        if declared : ∃ substitution : TypeSubst,
            annotation = abstractionAnnotation (request := request) (result := result) substitution then
          have sourceType : (abstractionAnnotation (request := request) (result := result) declared.choose).toHOL = type :=
            (congrArg Ty.toHOL declared.choose_spec).symm.trans typed
          sourceType ▸ abstractionInstance prior accepted proof other assignment declared.choose
        else (carrierModel prior accepted proof other assignment).constDen (.constant constant annotation typed)
      else if named : constant = result.output.representationConstant then
        if declared : ∃ substitution : TypeSubst,
            annotation = representationAnnotation (request := request) (result := result) substitution then
          have sourceType : (representationAnnotation (request := request) (result := result) declared.choose).toHOL = type :=
            (congrArg Ty.toHOL declared.choose_spec).symm.trans typed
          sourceType ▸ representationInstance prior accepted proof other assignment declared.choose
        else (carrierModel prior accepted proof other assignment).constDen (.constant constant annotation typed)
      else (carrierModel prior accepted proof other assignment).constDen (.constant constant annotation typed)

noncomputable def model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard (carrierModel prior accepted proof other assignment).Carrier
    (meanings prior accepted proof other assignment)

theorem model_carrier : (model prior accepted proof other assignment).Carrier =
    (carrierModel prior accepted proof other assignment).Carrier := rfl

theorem model_fullDomains : (model prior accepted proof other assignment).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem meanings_abstraction (substitution : TypeSubst) :
    (model prior accepted proof other assignment).constDen
      (.constant result.output.abstractionConstant
        (abstractionAnnotation (request := request) (result := result) substitution) rfl) =
      abstractionInstance prior accepted proof other assignment substitution := by
  classical
  have existsInstance : ∃ source : TypeSubst,
      abstractionAnnotation (request := request) (result := result) substitution =
        abstractionAnnotation (request := request) (result := result) source := ⟨substitution, rfl⟩
  simp only [model, HOL.HenkinModel.standard]
  simp only [meanings, dif_pos existsInstance]
  apply eq_of_heq
  exact (eqRec_heq _ _).trans
    (abstractionInstance_choice_independent prior accepted proof other assignment existsInstance.choose_spec.symm)

theorem meanings_representation (substitution : TypeSubst) :
    (model prior accepted proof other assignment).constDen
      (.constant result.output.representationConstant
        (representationAnnotation (request := request) (result := result) substitution) rfl) =
      representationInstance prior accepted proof other assignment substitution := by
  classical
  have existsInstance : ∃ source : TypeSubst,
      representationAnnotation (request := request) (result := result) substitution =
        representationAnnotation (request := request) (result := result) source := ⟨substitution, rfl⟩
  simp only [model, HOL.HenkinModel.standard]
  simp only [meanings, dif_neg (SourceTypeDefinitionTransport.admitted_constants_distinct accepted),
    dif_pos existsInstance]
  apply eq_of_heq
  exact (eqRec_heq _ _).trans
    (representationInstance_choice_independent prior accepted proof other assignment existsInstance.choose_spec.symm)

theorem meanings_other {constant : Const} {annotation : Ty} {type : HOL.Ty AtomicTy}
    (typed : annotation.toHOL = type)
    (notAbstraction : constant ≠ result.output.abstractionConstant)
    (notRepresentation : constant ≠ result.output.representationConstant) :
    (model prior accepted proof other assignment).constDen (.constant constant annotation typed) =
      (carrierModel prior accepted proof other assignment).constDen (.constant constant annotation typed) := by
  classical
  simp only [model, HOL.HenkinModel.standard, meanings, dif_neg notAbstraction, dif_neg notRepresentation]

theorem meanings_variable (sourceVar : SourceVar) {type : HOL.Ty AtomicTy}
    (typed : sourceVar.ty.toHOL = type) :
    (model prior accepted proof other assignment).constDen (.variable sourceVar typed) =
      (carrierModel prior accepted proof other assignment).constDen (.variable sourceVar typed) := by
  simp only [model, HOL.HenkinModel.standard, meanings]

theorem model_carrierModel_agreement :
    SourceAgreement context.signature (model prior accepted proof other assignment)
      (carrierModel prior accepted proof other assignment) where
  carriers := fun _ _ => rfl
  constants := by
    intro constant annotation type typed formed declared
    have different := licensed_old_constant accepted declared
    exact heq_of_eq (meanings_other prior accepted proof other assignment typed different.1 different.2)
  variableValues := by
    intro sourceVar type typed formed
    exact heq_of_eq (meanings_variable prior accepted proof other assignment sourceVar typed)

theorem model_old_agreement :
    SourceAgreement context.signature (model prior accepted proof other assignment)
      (prior.model other assignment) :=
  ConstantHistoryInstanceCoherence.sourceAgreement_trans
    (model_carrierModel_agreement prior accepted proof other assignment)
    (carrierModel_old_agreement prior accepted proof other assignment)

theorem model_models_old
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed context.signature term) :
    (model prior accepted proof other assignment).models formula ↔
      (prior.model other assignment).models formula :=
  (model_old_agreement prior accepted proof other assignment).models
    (prior.includes.1 TypeOp.function 2 functionArity)
    (model_fullDomains prior accepted proof other assignment)
    (prior.fullDomains other assignment) translated formed


private theorem apply_heq {A A' B B' : Type (w + 1)}
    (domain : A = A') (codomain : B = B') {function : A → B} {otherFunction : A' → B'}
    {argument : A} {otherArgument : A'} (functions : HEq function otherFunction)
    (arguments : HEq argument otherArgument) : HEq (function argument) (otherFunction otherArgument) := by
  cases domain
  cases codomain
  exact heq_of_eq (congrArg₂ (fun f x => f x) (eq_of_heq functions) (eq_of_heq arguments))

theorem meanings_abstraction_heq (substitution : TypeSubst) {type : HOL.Ty AtomicTy}
    (typed : (abstractionAnnotation (request := request) (result := result) substitution).toHOL = type) :
    HEq ((model prior accepted proof other assignment).constDen
      (.constant result.output.abstractionConstant
        (abstractionAnnotation (request := request) (result := result) substitution) typed))
      (abstraction prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)) := by
  cases typed
  exact (heq_of_eq (meanings_abstraction prior accepted proof other assignment substitution)).trans
    (abstractionInstance_heq prior accepted proof other assignment substitution)

theorem meanings_representation_heq (substitution : TypeSubst) {type : HOL.Ty AtomicTy}
    (typed : (representationAnnotation (request := request) (result := result) substitution).toHOL = type) :
    HEq ((model prior accepted proof other assignment).constDen
      (.constant result.output.representationConstant
        (representationAnnotation (request := request) (result := result) substitution) typed))
      (representation prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)) := by
  cases typed
  exact (heq_of_eq (meanings_representation prior accepted proof other assignment substitution)).trans
    (representationInstance_heq prior accepted proof other assignment substitution)

theorem model_abstraction_representation (substitution : TypeSubst)
    (value : HOL.Ty.denote.{0, w + 1} (model prior accepted proof other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution).toHOL) :
    (model prior accepted proof other assignment).constDen
        (.constant result.output.abstractionConstant
          (abstractionAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _))
      ((model prior accepted proof other assignment).constDen
        (.constant result.output.representationConstant
          (representationAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _)) value) = value := by
  have reps := apply_heq
    (new_carrier prior accepted proof other assignment substitution)
    (represented_carrier prior accepted proof other assignment substitution)
    (meanings_representation_heq prior accepted proof other assignment substitution (Ty.toHOL_function _ _))
    (cast_heq (new_carrier prior accepted proof other assignment substitution) value).symm
  have abstractions := apply_heq
    (represented_carrier prior accepted proof other assignment substitution)
    (new_carrier prior accepted proof other assignment substitution)
    (meanings_abstraction_heq prior accepted proof other assignment substitution (Ty.toHOL_function _ _)) reps
  rw [abstraction_representation] at abstractions
  exact eq_of_heq (abstractions.trans (cast_heq (new_carrier prior accepted proof other assignment substitution) value))


theorem instanceArguments_assignment_agreement (first second : Assignment.{w}) (substitution : TypeSubst)
    (agree : ∀ parameter ∈ (SourceTypeDefinitionTransport.sourceCarrierType request substitution).typeVariables,
      first parameter = second parameter) :
    instanceArguments prior accepted proof other first substitution =
      instanceArguments prior accepted proof other second substitution := by
  unfold instanceArguments
  apply List.map_congr_left
  intro parameter member
  change evaluate _ first (substitution.apply (.var parameter)) = evaluate _ second (substitution.apply (.var parameter))
  apply evaluate_parameter_agreement
  intro name occurs
  apply agree name
  exact (mem_typeVariablesList name _).mpr
    ⟨substitution.apply (.var parameter), List.mem_map.mpr ⟨parameter, member, rfl⟩, occurs⟩

theorem abstraction_assignment_agreement (first second : Assignment.{w}) (substitution : TypeSubst)
    (agree : ∀ parameter ∈ (abstractionAnnotation (request := request) (result := result) substitution).typeVariables,
      first parameter = second parameter) :
    HEq (abstractionInstance prior accepted proof other first substitution)
      (abstractionInstance prior accepted proof other second substitution) := by
  have arguments := instanceArguments_assignment_agreement prior accepted proof other first second substitution
    (by
      intro parameter occurs
      apply agree parameter
      simp only [abstractionAnnotation, Ty.function, Ty.typeVariables, Ty.typeVariablesList,
        Finset.union_empty, Finset.mem_union]
      exact Or.inr occurs)
  have maps : HEq
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other first substitution))
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other second substitution)) := by
    unfold instanceAssignment
    rw [arguments]
  exact (abstractionInstance_heq prior accepted proof other first substitution).trans
    (maps.trans (abstractionInstance_heq prior accepted proof other second substitution).symm)

theorem representation_assignment_agreement (first second : Assignment.{w}) (substitution : TypeSubst)
    (agree : ∀ parameter ∈ (representationAnnotation (request := request) (result := result) substitution).typeVariables,
      first parameter = second parameter) :
    HEq (representationInstance prior accepted proof other first substitution)
      (representationInstance prior accepted proof other second substitution) := by
  have arguments := instanceArguments_assignment_agreement prior accepted proof other first second substitution
    (by
      intro parameter occurs
      apply agree parameter
      simp only [representationAnnotation, Ty.function, Ty.typeVariables, Ty.typeVariablesList,
        Finset.union_empty, Finset.mem_union]
      exact Or.inl occurs)
  have maps : HEq
      (representation prior accepted proof other (instanceAssignment prior accepted proof other first substitution))
      (representation prior accepted proof other (instanceAssignment prior accepted proof other second substitution)) := by
    unfold instanceAssignment
    rw [arguments]
  exact (representationInstance_heq prior accepted proof other first substitution).trans
    (maps.trans (representationInstance_heq prior accepted proof other second substitution).symm)

theorem model_carrier_eq_atomic (assignment : Assignment.{w}) :
    (model prior accepted proof other assignment).Carrier =
      atomicCarrier (operators prior accepted proof other) assignment := by
  rw [model_carrier, Witnessed.carrierModel_carrier]

theorem model_symbol_local : ModelAssignmentSupport.SymbolLocal (model prior accepted proof other) := by
  intro first second type symbol agree
  have predecessor := prior.localSymbols (extend other (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other))
  cases symbol with
  | «variable» sourceVar typed =>
      rw [meanings_variable, meanings_variable]
      exact predecessor first second (.variable sourceVar typed) agree
  | constant constant annotation typed =>
      cases typed
      classical
      simp only [model, HOL.HenkinModel.standard, meanings]
      split
      · split
        · rename_i declared
          have supported : ∀ parameter ∈
              (abstractionAnnotation (request := request) (result := result) declared.choose).typeVariables,
              first parameter = second parameter := by
            have sourceAgree : ∀ parameter ∈ annotation.typeVariables, first parameter = second parameter := by
              simpa only [Ty.fromHOL_toHOL] using agree
            rw [declared.choose_spec] at sourceAgree
            exact sourceAgree
          exact (eqRec_heq _ _).trans
            ((abstraction_assignment_agreement prior accepted proof other first second declared.choose supported).trans
              (eqRec_heq _ _).symm)
        · exact predecessor first second (.constant constant annotation rfl) agree
      · split
        · split
          · rename_i declared
            have supported : ∀ parameter ∈
                (representationAnnotation (request := request) (result := result) declared.choose).typeVariables,
                first parameter = second parameter := by
              have sourceAgree : ∀ parameter ∈ annotation.typeVariables, first parameter = second parameter := by
                simpa only [Ty.fromHOL_toHOL] using agree
              rw [declared.choose_spec] at sourceAgree
              exact sourceAgree
            exact (eqRec_heq _ _).trans
              ((representation_assignment_agreement prior accepted proof other first second declared.choose supported).trans
                (eqRec_heq _ _).symm)
          · exact predecessor first second (.constant constant annotation rfl) agree
        · exact predecessor first second (.constant constant annotation rfl) agree


theorem instanceArguments_composition (assignment : Assignment.{w}) (first second : TypeSubst) :
    instanceArguments prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first =
    instanceArguments prior accepted proof other assignment (first.compose second) := by
  unfold instanceArguments
  rw [reindex_composition]

theorem abstractionInstance_composition (assignment : Assignment.{w}) (first second : TypeSubst) :
    HEq (abstractionInstance prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first)
      (abstractionInstance prior accepted proof other assignment (first.compose second)) := by
  have maps : HEq
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first))
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other assignment (first.compose second))) := by
    unfold instanceAssignment
    rw [instanceArguments_composition]
  exact (abstractionInstance_heq prior accepted proof other _ first).trans
    (maps.trans (abstractionInstance_heq prior accepted proof other assignment (first.compose second)).symm)

theorem representationInstance_composition (assignment : Assignment.{w}) (first second : TypeSubst) :
    HEq (representationInstance prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first)
      (representationInstance prior accepted proof other assignment (first.compose second)) := by
  have maps : HEq
      (representation prior accepted proof other (instanceAssignment prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first))
      (representation prior accepted proof other (instanceAssignment prior accepted proof other assignment (first.compose second))) := by
    unfold instanceAssignment
    rw [instanceArguments_composition]
  exact (representationInstance_heq prior accepted proof other _ first).trans
    (maps.trans (representationInstance_heq prior accepted proof other assignment (first.compose second)).symm)

theorem abstraction_meaning_of_annotation (assignment : Assignment.{w}) (substitution : TypeSubst)
    {annotation : Ty} (same : annotation = abstractionAnnotation (request := request) (result := result) substitution)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type) :
    HEq ((model prior accepted proof other assignment).constDen
      (.constant result.output.abstractionConstant annotation typed))
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other assignment substitution)) := by
  subst annotation
  exact meanings_abstraction_heq prior accepted proof other assignment substitution typed

theorem representation_meaning_of_annotation (assignment : Assignment.{w}) (substitution : TypeSubst)
    {annotation : Ty} (same : annotation = representationAnnotation (request := request) (result := result) substitution)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type) :
    HEq ((model prior accepted proof other assignment).constDen
      (.constant result.output.representationConstant annotation typed))
      (representation prior accepted proof other (instanceAssignment prior accepted proof other assignment substitution)) := by
  subst annotation
  exact meanings_representation_heq prior accepted proof other assignment substitution typed

/-- Original symbol substitution retains the abstraction identity and gives
exactly the map at the composed original parameter instance. -/
theorem abstraction_symbol_composition (assignment : Assignment.{w}) (first second : TypeSubst)
    {type : HOL.Ty AtomicTy}
    (typed : (abstractionAnnotation (request := request) (result := result) first).toHOL = type) :
    HEq ((model prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment)).constDen
      (.constant result.output.abstractionConstant (abstractionAnnotation (request := request) (result := result) first) typed))
      ((model prior accepted proof other assignment).constDen
        (second.symbolInstance (.constant result.output.abstractionConstant
          (abstractionAnnotation (request := request) (result := result) first) typed))) := by
  have maps : HEq
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first))
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other assignment (first.compose second))) := by
    unfold instanceAssignment
    rw [instanceArguments_composition]
  exact (meanings_abstraction_heq prior accepted proof other _ first typed).trans
    (maps.trans (abstraction_meaning_of_annotation prior accepted proof other assignment (first.compose second)
      (abstractionAnnotation_composition first second) _).symm)

theorem representation_symbol_composition (assignment : Assignment.{w}) (first second : TypeSubst)
    {type : HOL.Ty AtomicTy}
    (typed : (representationAnnotation (request := request) (result := result) first).toHOL = type) :
    HEq ((model prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment)).constDen
      (.constant result.output.representationConstant (representationAnnotation (request := request) (result := result) first) typed))
      ((model prior accepted proof other assignment).constDen
        (second.symbolInstance (.constant result.output.representationConstant
          (representationAnnotation (request := request) (result := result) first) typed))) := by
  have maps : HEq
      (representation prior accepted proof other (instanceAssignment prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first))
      (representation prior accepted proof other (instanceAssignment prior accepted proof other assignment (first.compose second))) := by
    unfold instanceAssignment
    rw [instanceArguments_composition]
  exact (meanings_representation_heq prior accepted proof other _ first typed).trans
    (maps.trans (representation_meaning_of_annotation prior accepted proof other assignment (first.compose second)
      (representationAnnotation_composition first second) _).symm)


/-- The actual carrier-changing predecessor retains its already-earned
source instances over the genuine later registry. -/
theorem carrierModel_instance_agreement_withTypes (later : Signature)
    (types : ∀ operator arity, result.context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity) (substitution : TypeSubst) :
    SourceAgreement (withTypes context.signature later)
      (carrierModel prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment))
      (reindexedModel substitution (carrierModel prior accepted proof other assignment)) := by
  have actual := prior.instances
    (extend other (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)) later
    (fun operator arity found => types operator arity ((admitSourceTypeInTheory_result accepted).1.1 operator arity found))
    assignment substitution
  rw [prior.freshOperators other (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted)] at actual
  exact actual

/-- Actual model carriers follow the original type reduct. -/
theorem model_reindex_carrier (substitution : TypeSubst) :
    (model prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment)).Carrier =
    (reindexedModel substitution (model prior accepted proof other assignment)).Carrier := by
  change (model prior accepted proof other
    (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment)).Carrier =
      fun atomic => HOL.Ty.denote (model prior accepted proof other assignment).Carrier (substitution.baseInstance atomic)
  rw [model_carrier_eq_atomic, model_carrier_eq_atomic]
  exact atomicCarrier_reindex (operators prior accepted proof other) substitution assignment

set_option backward.isDefEq.respectTransparency false in
/-- The complete installed source model is coherent at every original
licensed type instance, including old declarations at the new carrier types.
No coherence of the constructed family is assumed. -/
theorem model_instance_agreement_withTypes (later : Signature)
    (types : ∀ operator arity, result.context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (substitution : TypeSubst) :
    SourceAgreement (ConstantHistoryExpandedTypes.withTypes result.context.signature later)
      (model prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment))
      (reindexedModel substitution (model prior accepted proof other assignment)) := by
  have predecessor := carrierModel_instance_agreement_withTypes prior accepted proof other assignment later types substitution
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    exact congrArg (fun carrier => HOL.Ty.denote carrier type)
      (model_reindex_carrier prior accepted proof other assignment substitution)
  · intro constant annotation type typed formed declared
    by_cases abstractionName : constant = result.output.abstractionConstant
    · subst constant
      obtain ⟨first, rfl⟩ := licensed_abstraction_instance accepted declared
      change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
        (model prior accepted proof other assignment).Carrier type).symm
        ((model prior accepted proof other assignment).constDen
          (substitution.symbolInstance (.constant result.output.abstractionConstant _ typed))))
      exact (abstraction_symbol_composition prior accepted proof other assignment first substitution typed).trans
        (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm
    · by_cases representationName : constant = result.output.representationConstant
      · subst constant
        obtain ⟨first, rfl⟩ := licensed_representation_instance accepted declared
        change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
          (model prior accepted proof other assignment).Carrier type).symm
          ((model prior accepted proof other assignment).constDen
            (substitution.symbolInstance (.constant result.output.representationConstant _ typed))))
        exact (representation_symbol_composition prior accepted proof other assignment first substitution typed).trans
          (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm
      · have priorDeclared := old_constant_instance accepted abstractionName representationName declared
        have priorFormed := (typeFormed_eq_of_operators (ConstantHistoryExpandedTypes.withTypes result.context.signature later)
          (ConstantHistoryExpandedTypes.withTypes context.signature later) rfl annotation).mp formed
        have compared := predecessor.constants constant annotation typed priorFormed priorDeclared
        change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
          (model prior accepted proof other assignment).Carrier type).symm
          ((model prior accepted proof other assignment).constDen
            (substitution.symbolInstance (.constant constant annotation typed))))
        simp only [TypeSubst.symbolInstance]
        rw [meanings_other prior accepted proof other _ typed abstractionName representationName,
          meanings_other prior accepted proof other assignment _ abstractionName representationName]
        exact compared
  · intro sourceVar type typed formed
    have priorFormed := (typeFormed_eq_of_operators (ConstantHistoryExpandedTypes.withTypes result.context.signature later)
      (ConstantHistoryExpandedTypes.withTypes context.signature later) rfl sourceVar.ty).mp formed
    have compared := predecessor.variableValues sourceVar typed priorFormed
    change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
      (model prior accepted proof other assignment).Carrier type).symm
      ((model prior accepted proof other assignment).constDen
        (substitution.symbolInstance (.variable sourceVar typed))))
    simp only [TypeSubst.symbolInstance]
    rw [meanings_variable prior accepted proof other _ sourceVar typed,
      meanings_variable prior accepted proof other assignment _ _]
    exact compared


/-- The installed model follows source substitution at every licensed
current instance, with no extra coherence hypothesis. -/
theorem model_instance_agreement (substitution : TypeSubst) :
    SourceAgreement result.context.signature
      (model prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment))
      (reindexedModel substitution (model prior accepted proof other assignment)) :=
  model_instance_agreement_withTypes prior accepted proof other assignment result.context.signature
    (fun _ _ found => found) substitution

/-- Truth of an original formed sentence equals truth of its actual type
instance in the constructed installed model. -/
theorem model_models_instance (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (substitution : TypeSubst) {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed result.context.signature term) :
    (model prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment)).models formula ↔
      (model prior accepted proof other assignment).models
        (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula) :=
  ((model_instance_agreement prior accepted proof other assignment substitution).models
    ((admitSourceTypeInTheory_result accepted).1.1 TypeOp.function 2
      (prior.includes.1 TypeOp.function 2 functionArity))
    (model_fullDomains prior accepted proof other _) (reindexedModel_fullDomains _ _)
    translation formed).trans
      (reindexedModel_models substitution _ (model_fullDomains prior accepted proof other assignment) formula)

/-- Earned instance coherence transports the truth of a formed original
source sentence to each actual source type substitution. -/
theorem models_source_instance (primitives : Primitives initial)
    {term : DBTerm} {original instantiated : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop original)
    (formed : AnnotationsFormed result.context.signature term)
    (holds : ∀ changedAssignment, (model prior accepted proof other changedAssignment).models original)
    (substitution : TypeSubst)
    (instantiatedTranslation : TranslatesCompositionally [] ((TermSubst.mk substitution []).applyDB term) .prop instantiated) :
    (model prior accepted proof other assignment).models instantiated := by
  have natural := model_models_instance prior accepted proof other assignment primitives.functionArity
    substitution translation formed
  have typedInstance := ConstantHistoryInstanceCoherence.translation_type_instance result.context.signature
    primitives.equalityParameter ((admitSourceTypeInTheory_result accepted).1.2 _ _
      (prior.includes.2 _ _ primitives.equalityRegistered)) substitution translation formed
  rw [← typedInstance.unique_eq instantiatedTranslation]
  exact natural.mp (holds _)

/-- At the original declaration, installed source predicate denotation is
that of the actual prior model at the exact canonical parameter tuple. -/
theorem model_original_predicate_heq (primitives : Primitives initial) :
    HEq ((model prior accepted proof other assignment).denote
      (TypeAdmission.admittedImage accepted).predicateTerm (fun index => nomatch index))
      ((prior.model other (instanceAssignment prior accepted proof other assignment TypeSubst.empty)).denote
        (TypeAdmission.admittedImage accepted).predicateTerm (fun index => nomatch index)) := by
  have formed := (admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1
  have original := (model_old_agreement prior accepted proof other assignment).denote
    (prior.includes.1 _ _ primitives.functionArity) (model_fullDomains prior accepted proof other assignment)
    (prior.fullDomains other assignment) (TypeAdmission.admittedImage accepted).predicateTranslated formed
    (by intro type member; cases member) (fun index => nomatch index) (fun index => nomatch index)
    (by intro type index; nomatch index)
  have supported := ModelAssignmentSupport.denote_parameter_agreement (prior.operators other) (prior.model other)
    (prior.carrier other) (prior.fullDomains other) (prior.localSymbols other) assignment
    (instanceAssignment prior accepted proof other assignment TypeSubst.empty)
    (TypeAdmission.admittedImage accepted).predicateTranslated
    (by
      intro parameter member
      rw [instanceAssignment_agrees prior accepted proof other assignment TypeSubst.empty parameter
        (List.mem_toFinset.mp ((UniformTypeDefinitionFamily.admitted_parameter_guards accepted).2.1.symm ▸ member))]
      simp only [reindex, TypeSubst.apply_empty, evaluate_var])
    (by intro parameter member; simp [ModelAssignmentSupport.contextSupport, Ty.typeVariablesList] at member)
    (fun index => nomatch index) (fun index => nomatch index) (by intro type index; nomatch index)
  exact original.trans supported

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

set_option backward.isDefEq.respectTransparency false in
/-- The retained original predicate is exactly the abstraction/representation
law of the genuine witnessed subtype. -/
theorem model_original_predicate_law (primitives : Primitives initial)
    (value : HOL.Ty.denote.{0, w + 1} (model prior accepted proof other assignment).Carrier result.core.witness.ty.toHOL) :
    (((model prior accepted proof other assignment).denote
      (TypeAdmission.admittedImage accepted).predicateTerm (fun index => nomatch index)) value).down ↔
      (model prior accepted proof other assignment).constDen
          (.constant result.output.representationConstant
            (representationAnnotation (request := request) (result := result) TypeSubst.empty)
            (show (representationAnnotation (request := request) (result := result) TypeSubst.empty).toHOL =
              HOL.Ty.arr (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty).toHOL result.core.witness.ty.toHOL from by
                simpa only [representationAnnotation, TypeSubst.apply_empty] using
                  Ty.toHOL_function (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty) result.core.witness.ty))
        ((model prior accepted proof other assignment).constDen
          (.constant result.output.abstractionConstant
            (abstractionAnnotation (request := request) (result := result) TypeSubst.empty)
            (show (abstractionAnnotation (request := request) (result := result) TypeSubst.empty).toHOL =
              HOL.Ty.arr result.core.witness.ty.toHOL (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty).toHOL from by
                simpa only [abstractionAnnotation, TypeSubst.apply_empty] using
                  Ty.toHOL_function result.core.witness.ty (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty))) value) = value := by
  have represented := represented_carrier prior accepted proof other assignment TypeSubst.empty
  simp only [TypeSubst.apply_empty] at represented
  have values := apply_heq represented rfl (model_original_predicate_heq prior accepted proof other assignment primitives)
    (cast_heq represented value).symm
  have predicate : (((model prior accepted proof other assignment).denote
      (TypeAdmission.admittedImage accepted).predicateTerm (fun index => nomatch index)) value).down =
      TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
        (prior.model other (instanceAssignment prior accepted proof other assignment TypeSubst.empty))
        (cast represented value) := by
    exact (congrArg (fun truth : ULift.{w + 1, 0} Prop => truth.down) (eq_of_heq values)).trans
      (congrArg (fun function => (function (cast represented value)).down)
        ((prior.model other (instanceAssignment prior accepted proof other assignment TypeSubst.empty)).denote_closed_valuation_eq
          (TypeAdmission.admittedImage accepted).predicateTerm _ _))
  rw [predicate]
  have abstractions := apply_heq represented
    (new_carrier prior accepted proof other assignment TypeSubst.empty)
    (meanings_abstraction_heq prior accepted proof other assignment TypeSubst.empty
      (by simpa only [abstractionAnnotation, TypeSubst.apply_empty] using
        Ty.toHOL_function result.core.witness.ty (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty)))
    (cast_heq represented value).symm
  have reps := apply_heq (new_carrier prior accepted proof other assignment TypeSubst.empty) represented
    (meanings_representation_heq prior accepted proof other assignment TypeSubst.empty
      (by simpa only [representationAnnotation, TypeSubst.apply_empty] using
        Ty.toHOL_function (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty) result.core.witness.ty)) abstractions
  exact (Witnessed.predicate_iff_representation_abstraction prior accepted proof other
    (instanceAssignment prior accepted proof other assignment TypeSubst.empty) _).trans
    (equality_heq represented reps (cast_heq represented value).symm).symm

theorem model_comparison_agreement :
    SourceAgreement (comparisonSignature (context := context) (result := result))
      (model prior accepted proof other assignment) (carrierModel prior accepted proof other assignment) where
  carriers := fun _ _ => rfl
  constants := by
    intro constant annotation type typed formed declared
    have oldDeclaration : ConstantInstance context.signature constant annotation := declared
    have different := licensed_old_constant accepted oldDeclaration
    exact heq_of_eq (meanings_other prior accepted proof other assignment typed different.1 different.2)
  variableValues := by
    intro sourceVar type typed formed
    exact heq_of_eq (meanings_variable prior accepted proof other assignment sourceVar typed)


theorem model_instance_predicate_same (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    (model prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v) =
    (carrierModel prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v) := by
  apply eq_of_heq
  apply (model_comparison_agreement prior accepted proof other assignment).denote
    ((comparisonSignature_includes accepted).1 TypeOp.function 2
      (SourceTypeDefinitionTransport.admitted_function_arity accepted))
    (model_fullDomains prior accepted proof other assignment)
    (carrierModel_fullDomains prior accepted proof other assignment)
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
    (primitives : Primitives initial)
    (substitution : TypeSubst) :
    HEq ((carrierModel prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v))
      ((prior.model other (instanceAssignment prior accepted proof other assignment substitution)).denote
        (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v)) := by
  let next := extend other (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)
  let changed := reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment
  have originalAnnotations := (admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1
  have historyAgreement := prior.instances next context.signature (fun _ _ found => found) assignment substitution
  rw [prior.freshOperators other (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted)] at historyAgreement
  have values := historyAgreement.denote
    (prior.includes.1 TypeOp.function 2 primitives.functionArity)
    (prior.fullDomains next changed)
    (reindexedModel_fullDomains substitution (prior.model next assignment))
    (TypeAdmission.admittedImage accepted).predicateTranslated originalAnnotations
    (by intro type member; cases member) (fun v => nomatch v) (fun v => nomatch v)
    (by intro type index; nomatch index)
  have normalizedValues : HEq
      ((prior.model next changed).denote (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v))
      ((reindexedModel substitution (prior.model next assignment)).denote
        (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v)) :=
    (heq_of_eq ((prior.model next changed).denote_closed_valuation_eq _ _ _)).trans
      (values.trans (heq_of_eq ((reindexedModel substitution
        (prior.model next assignment)).denote_closed_valuation_eq _ _ _)))
  have mapped := denote_reduct_heq (prior.model next assignment)
    (prior.fullDomains next assignment) substitution (TypeAdmission.admittedImage accepted).predicateTerm
  have translated := ConstantHistoryInstanceCoherence.translation_type_instance context.signature primitives.equalityParameter
    (prior.includes.2 Const.equality _ primitives.equalityRegistered) substitution
    (TypeAdmission.admittedImage accepted).predicateTranslated originalAnnotations
  have same := translated.unique (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTranslated
  have mappedActual := ConstantHistoryInstanceCoherence.denote_closed_heq (prior.model next assignment)
    same.1 same.2 (fun v => nomatch v) (fun v => nomatch v)
  have oldOperators := prior.freshModels other
    (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted) changed
  have unchanged := oldOperators.denote
    (prior.includes.1 TypeOp.function 2 primitives.functionArity)
    (prior.fullDomains next changed) (prior.fullDomains other changed)
    (TypeAdmission.admittedImage accepted).predicateTranslated originalAnnotations
    (by intro type member; cases member) (fun v => nomatch v) (fun v => nomatch v)
    (by intro type index; nomatch index)
  have parameters := ModelAssignmentSupport.denote_parameter_agreement (prior.operators other) (prior.model other)
    (prior.carrier other) (prior.fullDomains other) (prior.localSymbols other)
    changed (instanceAssignment prior accepted proof other assignment substitution)
    (TypeAdmission.admittedImage accepted).predicateTranslated
    (by
      intro parameter occurs
      exact (instanceAssignment_agrees prior accepted proof other assignment substitution parameter
        (List.mem_toFinset.mp ((UniformTypeDefinitionFamily.admitted_parameter_guards accepted).2.1.symm ▸ occurs))).symm)
    (by intro parameter occurs; simp [ModelAssignmentSupport.contextSupport, Ty.typeVariablesList] at occurs)
    (fun v => nomatch v) (fun v => nomatch v) (by intro type index; nomatch index)
  have normalized : HEq
      ((prior.model other changed).denote (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v))
      ((prior.model other (instanceAssignment prior accepted proof other assignment substitution)).denote
        (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v)) :=
    (heq_of_eq ((prior.model other changed).denote_closed_valuation_eq _ _ _)).trans
    (parameters.trans (heq_of_eq ((prior.model other
      (instanceAssignment prior accepted proof other assignment substitution)).denote_closed_valuation_eq _ _ _)))
  have instanceValues := compose_closed (prior.model next assignment)
    (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (TypeAdmission.admittedImage accepted).predicateTerm)
    _ _ mappedActual.symm (mapped.symm.trans normalizedValues.symm)

  exact instanceValues.trans (unchanged.trans normalized)


theorem model_instance_predicate (primitives : Primitives initial) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution))
    (value : HOL.Ty.denote.{0, w + 1} (model prior accepted proof other assignment).Carrier
      (substitution.apply result.core.witness.ty).toHOL) :
    (((model prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v)) value).down =
    TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
      (prior.model other (instanceAssignment prior accepted proof other assignment substitution))
      (cast (represented_carrier prior accepted proof other assignment substitution) value) := by
  have functions := compose_closed (carrierModel prior accepted proof other assignment)
    (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm _ _
    (heq_of_eq (model_instance_predicate_same prior accepted proof other assignment substitution formedCarrier))
    (carrierModel_instance_predicate_heq prior accepted proof other assignment
      primitives substitution)
  have arguments := (cast_heq (represented_carrier prior accepted proof other assignment substitution) value).symm
  have outputs := apply_heq (represented_carrier prior accepted proof other assignment substitution) rfl functions arguments
  apply Eq.trans (congrArg (fun truth : ULift.{w + 1, 0} Prop => truth.down) (eq_of_heq outputs))
  exact congrArg (fun function => (function
    (cast (represented_carrier prior accepted proof other assignment substitution) value)).down)
    ((prior.model other (instanceAssignment prior accepted proof other assignment substitution)).denote_closed_valuation_eq
      (TypeAdmission.admittedImage accepted).predicateTerm _ _)

theorem model_predicate_iff_representation_abstraction (primitives : Primitives initial) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution))
    (value : HOL.Ty.denote.{0, w + 1} (model prior accepted proof other assignment).Carrier
      (substitution.apply result.core.witness.ty).toHOL) :
    (((model prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v)) value).down ↔
      (model prior accepted proof other assignment).constDen
          (.constant result.output.representationConstant
            (representationAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _))
        ((model prior accepted proof other assignment).constDen
          (.constant result.output.abstractionConstant
            (abstractionAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _)) value) = value := by
  rw [model_instance_predicate prior accepted proof other assignment primitives substitution formedCarrier value]
  have abstractions := apply_heq
    (represented_carrier prior accepted proof other assignment substitution)
    (new_carrier prior accepted proof other assignment substitution)
    (meanings_abstraction_heq prior accepted proof other assignment substitution (Ty.toHOL_function _ _))
    (cast_heq (represented_carrier prior accepted proof other assignment substitution) value).symm
  have reps := apply_heq
    (new_carrier prior accepted proof other assignment substitution)
    (represented_carrier prior accepted proof other assignment substitution)
    (meanings_representation_heq prior accepted proof other assignment substitution (Ty.toHOL_function _ _)) abstractions
  exact (predicate_iff_representation_abstraction prior accepted proof other
    (instanceAssignment prior accepted proof other assignment substitution) _).trans
    (equality_heq (represented_carrier prior accepted proof other assignment substitution) reps
      (cast_heq (represented_carrier prior accepted proof other assignment substitution) value).symm).symm

set_option backward.isDefEq.respectTransparency false in
theorem model_models_abstractionRepresentation (substitution : TypeSubst) :
    (model prior accepted proof other assignment).models
      (SourceTypeDefinitionTransport.abstractionRepresentationFormula (request := request) (result := result) substitution) := by
  change (model prior accepted proof other assignment).Eqv _ _ _
  apply (eqv_iff_eq _ (model_fullDomains prior accepted proof other assignment) _ _ _).mpr
  exact model_abstraction_representation prior accepted proof other assignment substitution _

set_option backward.isDefEq.respectTransparency false in
theorem model_models_representationAbstraction (primitives : Primitives initial) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    (model prior accepted proof other assignment).models
      (SourceTypeDefinitionTransport.representationAbstractionFormula accepted substitution) := by
  let value := (model prior accepted proof other assignment).constDen
    (.variable ⟨Name.global "r", (SourceTypeDefinitionTransport.instanceTerm substitution result.core.witness).ty⟩ rfl)
  have meaning : (((model prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v)) value).down ↔
      (model prior accepted proof other assignment).Eqv
        (SourceTypeDefinitionTransport.instanceTerm substitution result.core.witness).ty.toHOL
        ((model prior accepted proof other assignment).constDen
          (.constant result.output.representationConstant
            (representationAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _))
          ((model prior accepted proof other assignment).constDen
            (.constant result.output.abstractionConstant
              (abstractionAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _)) value)) value :=
    (model_predicate_iff_representation_abstraction prior accepted proof other assignment
      primitives substitution formedCarrier value).trans
      (eqv_iff_eq _ (model_fullDomains prior accepted proof other assignment) _ _ _).symm
  convert meaning using 1
  simp only [SourceTypeDefinitionTransport.representationAbstractionFormula,
    SourceTypeDefinitionTransport.abstractionTerm, SourceTypeDefinitionTransport.representationTerm,
    abstractionAnnotation, representationAnnotation, equalityLambda, HOL.HenkinModel.models,
    HOL.PreModel.models, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend, HOL.PreModel.Eqv, value]
  apply iff_congr
  · exact iff_of_eq (congrArg (fun function => (function value).down)
      ((model prior accepted proof other assignment).denote_closed_valuation_eq
        (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm _ _))
  · rfl


/-- Every original retained new equation is true at every source type
instance, using original admission licences and the earned model naturality. -/
theorem type_equation_instances (primitives : Primitives initial) (substitution : TypeSubst)
    {first second : HOL.ClosedFormula Symbol}
    (firstTranslation : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.abstractionRepresentationTheorem.sequent.concl.term) .prop first)
    (secondTranslation : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.representationAbstractionTheorem.sequent.concl.term) .prop second) :
    (model prior accepted proof other assignment).models first ∧
      (model prior accepted proof other assignment).models second := by
  have firstOriginal := (SourceTypeDefinitionTransport.abstractionRepresentation_translated accepted TypeSubst.empty).of_term_eq
    (TermSubst.typeInstance_identity _)
  have secondOriginal := (SourceTypeDefinitionTransport.representationAbstraction_translated accepted TypeSubst.empty).of_term_eq
    (TermSubst.typeInstance_identity _)
  have formed := type_equations_formed accepted (prior.includes.1 _ _ primitives.functionArity)
    primitives.equalityParameter (prior.includes.2 _ _ primitives.equalityRegistered)
  have originalCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty) :=
    (result.context.constantTypes _ _ (UniformTypeDefinitionInstances.new_constants_registered accepted).1).function_components _ |>.2
  constructor
  · exact models_source_instance prior accepted proof other assignment primitives firstOriginal formed.1
      (fun changedAssignment => model_models_abstractionRepresentation prior accepted proof other changedAssignment TypeSubst.empty)
      substitution firstTranslation
  · exact models_source_instance prior accepted proof other assignment primitives secondOriginal formed.2
      (fun changedAssignment => model_models_representationAbstraction prior accepted proof other changedAssignment primitives
        TypeSubst.empty originalCarrier) substitution secondTranslation

end Mettapedia.Languages.HOLLight.TypeDefinitionModels
