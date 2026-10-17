import Mettapedia.Languages.HOLLight.ConstantHistoryInstanceCoherence
import Mettapedia.Languages.HOLLight.ProofSystem

/-!
# Uniform source type families from admitted witnessed predicates

Each tuple of the original parameter arity constructs a genuine predicate
subtype in the original preceding constant-history model. Syntactic proof of
the retained existence application supplies nonemptiness. The chosen domain
inhabitant depends on the subtype, rather than on unused parameters of the
source witness. Both defining maps therefore use one uniform family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.UniformTypeDefinitionFamily

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters

universe w

/-- The original equations of actual prior constant declarations, at every
source type instance. These are syntactic theory sentences, not a model-truth
assumption about the new family. -/
def definitionTheory {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final) : HOL.ClosedTheorySet Symbol :=
  {formula | ∃ result ∈ history.records, ∃ substitution : TypeSubst,
    TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.definitionTheorem.sequent.concl.term)
      .prop formula}

theorem models_definitionTheory {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    ∀ formula ∈ definitionTheory history, (history.extendModel M).models formula := by
  rintro formula ⟨result, member, substitution, translated⟩
  exact history.models_record_equation M member substitution translated

/-- Reconstruct the actual admitted predecessor history at the supplied
complete semantic parameter assignment. -/
noncomputable def priorModel {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  history.extendModel (initialModel other assignment)

theorem priorModel_carrier {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (priorModel history other assignment).Carrier = atomicCarrier other assignment :=
  history.carrier _

theorem priorModel_fullDomains {initial final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (priorModel history other assignment).FullDomains := history.fullDomains _ (initialModel_fullDomains _ _)

/-- An actual proof over the original prior definition equations earns the
retained existence application's truth for every assignment. -/
theorem existence_models {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (priorModel history other assignment).models (TypeAdmission.admittedImage accepted).formula :=
  provable_models proof _
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _ (priorModel_fullDomains history other assignment))
    (models_definitionTheory history _)

/-- The original arity/support guards are earned from the original admission
and refer to the exact retained predicate and witness. -/
theorem admitted_parameter_guards {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    request.typeVariables.Nodup ∧ request.typeVariables.toFinset = result.core.predicate.term.typeVariables ∧
      request.existence.sequent.hyp = ∅ := by
  have admitted := (admitSourceTypeInTheory_result accepted).2.1
  have application := (admitTypeInTheory_result admitted).1
  have checkResult := (admitTypeInTheory_result admitted).2.2.2.2.2.1
  obtain ⟨predicate, witness, sourceApplication, boolean, checkedSource, emptyHyp, closed, nodup, support, output⟩ :=
    checkTypeOperatorDefinition_result checkResult
  have viewFirst := CanonicalTerm.applicationView?_eq_some _ _ _ application
  have viewSecond := CanonicalTerm.applicationView?_eq_some _ _ _ sourceApplication
  have sameView := Option.some.inj (viewFirst.symm.trans viewSecond)
  have samePredicate := congrArg CanonicalTerm.ApplicationView.function sameView
  exact ⟨nodup, support.trans (congrArg (fun term : CanonicalTerm => term.term.typeVariables) samePredicate).symm, emptyHyp⟩

/-- An actual original source-kernel derivation supplies the existence proof
required by the uniform construction. -/
theorem existence_proof_of_kernel_derives {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (derived : Mettapedia.Logic.Derives (HOLLight.Rule emptyAxiomPolicy) request.existence) :
    HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula := by
  have derivation := derives_shared emptyAxiomPolicy derived
  have provable := derives_compositionallyProvable variableFreeSubstitutionClosed_empty derivation
    (by
      intro tagged member
      rw [axioms_eq_empty_of_emptyAxiomPolicy derivation] at member
      exact absurd member (Finset.notMem_empty _))
  obtain ⟨formula, translated, proven⟩ := provable
  have same : formula = (TypeAdmission.admittedImage accepted).formula :=
    eq_of_heq (translated.unique (TypeAdmission.admittedImage accepted).conclusionTranslated).2
  subst formula
  apply HOL.ClosedTheorySet.provable_mono _ proven
  rintro sentence (empty | hypotheses)
  · exact absurd empty (Set.notMem_empty _)
  · obtain ⟨term, member, _⟩ := hypotheses
    rw [(admitted_parameter_guards accepted).2.2] at member
    exact absurd member (Finset.notMem_empty _)

/-- A genuine accepted original source-kernel graph supplies this same
syntactic existence proof. The graph checker and retained request are
unchanged. -/
theorem existence_proof_of_kernel_checked {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    {certificate : ProofSystem.Certificate}
    (checked : (ProofSystem.checker emptyAxiomPolicy).check request.existence certificate = true) :
    HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula :=
  existence_proof_of_kernel_derives history accepted
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound request.existence certificate checked)

/-- The list layout uses the original ordered parameter names and the actual
domain tuple; no argument is inferred from its position's meaning. -/
def tupleAssignment : List Name → List Domain.{w} → Assignment.{w}
  | parameter :: parameters, argument :: arguments =>
      Function.update (tupleAssignment parameters arguments) parameter argument
  | _, _ => fun _ => proposition

theorem tupleAssignment_mapped (parameters : List Name) (assignment : Assignment.{w}) :
    ∀ parameter ∈ parameters,
      tupleAssignment parameters (parameters.map assignment) parameter = assignment parameter := by
  induction parameters with
  | nil => simp
  | cons head tail ih =>
      intro parameter member
      simp only [List.map_cons, tupleAssignment]
      by_cases same : parameter = head
      · subst parameter
        simp only [Function.update_self]
      · simp only [Function.update_of_ne same]
        exact ih parameter ((List.mem_cons.mp member).resolve_left same)

/-- The actual subtype supplies its own canonical inhabitant. The source
witness proves nonemptiness; proof-irrelevance prevents a different proof of
nonemptiness from changing this selected domain. -/
noncomputable def inhabitedSubtype (carrier : Type (w + 1)) (predicate : carrier → Prop)
    (nonempty : Nonempty {value // predicate value}) : Domain.{w} :=
  ⟨{value // predicate value}, Classical.choice nonempty⟩

theorem inhabitedSubtype_congr {firstCarrier secondCarrier : Type (w + 1)}
    (carriers : firstCarrier = secondCarrier)
    {firstPredicate : firstCarrier → Prop} {secondPredicate : secondCarrier → Prop}
    (predicates : HEq firstPredicate secondPredicate)
    (firstNonempty : Nonempty {value // firstPredicate value})
    (secondNonempty : Nonempty {value // secondPredicate value}) :
    inhabitedSubtype firstCarrier firstPredicate firstNonempty =
      inhabitedSubtype secondCarrier secondPredicate secondNonempty := by
  cases carriers
  have same := eq_of_heq predicates
  subst secondPredicate
  rfl

noncomputable def predicateDomain {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) : Domain.{w} :=
  inhabitedSubtype _ (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
      (priorModel history other assignment))
    ⟨⟨TypeAdmission.representedWitness (TypeAdmission.admittedImage accepted)
      (priorModel history other assignment),
      TypeAdmission.witness_valid _ _ (existence_models history accepted proof other assignment)⟩⟩

/-- The actual represented type has no parameter missing from the original
predicate's declared support. -/
theorem represented_support {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    result.core.witness.ty.typeVariables ⊆ request.typeVariables.toFinset := by
  intro parameter member
  rw [(admitted_parameter_guards accepted).2.1]
  have support := ModelAssignmentSupport.translation_type_support
    (TypeAdmission.admittedImage accepted).predicateTranslated
  have occurrence : parameter ∈ (Ty.fromHOL (.arr result.core.witness.ty.toHOL .prop)).typeVariables := by
    simpa only [Ty.fromHOL, Ty.fromHOL_toHOL, Ty.function, Ty.bool, Ty.typeVariables,
      Ty.typeVariablesList, Finset.union_empty] using member
  simpa only [ModelAssignmentSupport.contextSupport, List.map_nil, Ty.typeVariablesList,
    Finset.union_empty] using support occurrence

private theorem predicate_function_heq {firstCarrier secondCarrier : Type (w + 1)}
    (carriers : firstCarrier = secondCarrier)
    {first : firstCarrier → ULift.{w + 1, 0} Prop} {second : secondCarrier → ULift.{w + 1, 0} Prop}
    (functions : HEq first second) : HEq (fun value => (first value).down) (fun value => (second value).down) := by
  cases carriers
  exact heq_of_eq (congrArg (fun function => fun value => (function value).down) (eq_of_heq functions))

/-- Actual predicate subtypes and their canonical inhabitants depend only
on the original admitted parameter tuple, not on unused assignments or
unused parameters of the witness. -/
theorem predicateDomain_assignment_agreement {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (first second : Assignment.{w})
    (agree : ∀ parameter ∈ request.typeVariables, first parameter = second parameter) :
    predicateDomain history accepted proof other first = predicateDomain history accepted proof other second := by
  have predicateAgreement : ∀ parameter ∈ result.core.predicate.term.typeVariables,
      first parameter = second parameter := by
    intro parameter member
    apply agree parameter
    rw [← (admitted_parameter_guards accepted).2.1] at member
    exact List.mem_toFinset.mp member
  have typeAgreement : ∀ parameter ∈ result.core.witness.ty.typeVariables,
      first parameter = second parameter := by
    intro parameter member
    exact agree parameter (List.mem_toFinset.mp (represented_support accepted member))
  have carriers : HOL.Ty.denote.{0, w + 1} (priorModel history other first).Carrier result.core.witness.ty.toHOL =
      HOL.Ty.denote.{0, w + 1} (priorModel history other second).Carrier result.core.witness.ty.toHOL := by
    rw [priorModel_carrier, priorModel_carrier]
    exact ModelAssignmentSupport.carrier_parameter_agreement other first second _ typeAgreement
  have values := ModelAssignmentSupport.denote_parameter_agreement other (priorModel history other)
    (priorModel_carrier history other) (priorModel_fullDomains history other)
    (history_initial_symbol_local history other) first second
    (TypeAdmission.admittedImage accepted).predicateTranslated predicateAgreement
    (by intro parameter member; simp [ModelAssignmentSupport.contextSupport, Ty.typeVariablesList] at member)
    (fun index => nomatch index) (fun index => nomatch index) (by intro type index; nomatch index)
  apply inhabitedSubtype_congr carriers
  apply predicate_function_heq carriers
  exact (heq_of_eq ((priorModel history other first).denote_closed_valuation_eq _ _ _)).trans
    (values.trans (heq_of_eq ((priorModel history other second).denote_closed_valuation_eq _ _ _)))

/-- Wrong arities are refused explicitly; every admitted tuple obtains the
actual witnessed subtype from its complete semantic parameter assignment. -/
noncomputable def family? {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (arguments : List Domain.{w}) : Option Domain.{w} :=
  if arguments.length = request.typeVariables.length then
    some (predicateDomain history accepted proof other (tupleAssignment request.typeVariables arguments))
  else none

theorem family?_wrong_arity {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (arguments : List Domain.{w})
    (wrong : arguments.length ≠ request.typeVariables.length) :
    family? history accepted proof other arguments = none := by
  simp [family?, wrong]

/-- Total operator-family semantics retain the ordinary inhabited fallback
only on unlicensed arities; `family?` remains the admission operation. -/
noncomputable def family {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (arguments : List Domain.{w}) : Domain.{w} :=
  (family? history accepted proof other arguments).getD proposition

theorem family_valid {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (arguments : List Domain.{w})
    (arity : arguments.length = request.typeVariables.length) :
    family history accepted proof other arguments =
      predicateDomain history accepted proof other (tupleAssignment request.typeVariables arguments) := by
  simp [family, family?, arity]

theorem family_at_assignment {initial context : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial context)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    family history accepted proof other (request.typeVariables.map assignment) =
      predicateDomain history accepted proof other assignment := by
  rw [family_valid _ _ _ _ _ (List.length_map _)]
  exact predicateDomain_assignment_agreement history accepted proof other _ _
    (tupleAssignment_mapped _ _)

variable {initial context : TheoryContext}
  (history : DefinitionHistoryModels.ConstantHistory initial context)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

/-- The original predicate subtype's abstraction uses its canonical valid
inhabitant for values outside the predicate. -/
noncomputable def abstraction :
    HOL.Ty.denote.{0, w + 1} (priorModel history other assignment).Carrier result.core.witness.ty.toHOL →
      (predicateDomain history accepted proof other assignment).Carrier :=
  HOL.WitnessedTypeDefinition.abstraction
    (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted) (priorModel history other assignment))
    (predicateDomain history accepted proof other assignment).inhabitant.val
    (predicateDomain history accepted proof other assignment).inhabitant.property

def representation : (predicateDomain history accepted proof other assignment).Carrier →
    HOL.Ty.denote.{0, w + 1} (priorModel history other assignment).Carrier result.core.witness.ty.toHOL :=
  HOL.WitnessedTypeDefinition.representation

/-- The first actual witnessed definition law holds uniformly over all
complete original parameter assignments and all new-carrier values. -/
theorem abstraction_representation (value : (predicateDomain history accepted proof other assignment).Carrier) :
    abstraction history accepted proof other assignment
      (representation history accepted proof other assignment value) = value :=
  HOL.WitnessedTypeDefinition.abstraction_representation _ _ _ value

/-- The second actual witnessed definition law retains the original
predicate's meaning, including values outside its subtype. -/
theorem predicate_iff_representation_abstraction
    (value : HOL.Ty.denote.{0, w + 1} (priorModel history other assignment).Carrier result.core.witness.ty.toHOL) :
    TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted) (priorModel history other assignment) value ↔
      representation history accepted proof other assignment
        (abstraction history accepted proof other assignment value) = value :=
  HOL.WitnessedTypeDefinition.predicate_iff_representation_abstraction _ _ _ value

/-- Reconstructing the prior original constant history over the actual new
operator family gives its full source carriers and meanings. This phase does
not yet install the new abstraction/representation symbols. -/
noncomputable def carrierModel : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  priorModel history (extend other (SourceTypeDefinitionTransport.operator request)
    (family history accepted proof other)) assignment

/-- The original carrier schema receives the same complete predicate subtype
for every semantic parameter assignment, inside the full source operator
table rather than a separate syntax. -/
theorem carrierModel_new :
    HOL.Ty.denote.{0, w + 1} (carrierModel history accepted proof other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty).toHOL =
      (predicateDomain history accepted proof other assignment).Carrier := by
  rw [carrierModel, priorModel_carrier]
  rw [← evaluate_toHOL]
  apply congrArg Domain.Carrier
  have sourceShape : SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty =
      .op (SourceTypeDefinitionTransport.operator request) (request.typeVariables.map Ty.var) := by
    simp [SourceTypeDefinitionTransport.sourceCarrierType]
  rw [sourceShape, evaluate_op,
    primitiveFamilies_extend other _ _ (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2,
    extend_new]
  have arguments : (request.typeVariables.map Ty.var).map
      (evaluate (extend (primitiveFamilies other) (SourceTypeDefinitionTransport.operator request)
        (family history accepted proof other)) assignment) = request.typeVariables.map assignment := by
    simp only [List.map_map, Function.comp_def, evaluate_var]
  rw [arguments]
  exact family_at_assignment history accepted proof other assignment

/-- All originally formed source meanings survive the actual uniform
operator-family extension and the complete preceding constant history. -/
theorem carrierModel_old_agreement
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2) :
    SourceAgreement context.signature (carrierModel history accepted proof other assignment)
      (priorModel history other assignment) :=
  constantHistory_operator_agreement history functionArity other _ _
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted) assignment

theorem carrierModel_models_old
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed context.signature term) :
    (carrierModel history accepted proof other assignment).models formula ↔
      (priorModel history other assignment).models formula :=
  (carrierModel_old_agreement history accepted proof other assignment functionArity).models
    (history.includes.1 TypeOp.function 2 functionArity)
    (priorModel_fullDomains history _ assignment) (priorModel_fullDomains history other assignment) translated formed

namespace Controls

open DefinitionAdapters.ContextControls

def polymorphicPredicateSource : SourceTerm :=
  .app (.const Const.equality (Ty.equality ModelInterpretation.Controls.polymorphicIdentityTerm.ty))
    ModelInterpretation.Controls.polymorphicIdentitySource

def polymorphicExistence : Theorem := Theorem.emptyResult ∅
  (CanonicalTerm.equalityOfSameType ModelInterpretation.Controls.polymorphicIdentityTerm
    ModelInterpretation.Controls.polymorphicIdentityTerm rfl)

def polymorphicRequest : TypeOperatorDefinitionRequest :=
  { typeName := Name.global "uniformIdentityFunction"
    abstractionName := Name.global "absUniformIdentityFunction"
    representationName := Name.global "repUniformIdentityFunction"
    typeVariables := sortedParameters polymorphicPredicateSource
    predicateSource := polymorphicPredicateSource
    existence := polymorphicExistence }

def polymorphicCertificates : InstanceWitnesses := fun _ _ =>
  ⟨[(equalityParameter, ModelInterpretation.Controls.polymorphicIdentityTerm.ty)]⟩

/-- The parameter-bearing type request is admitted after the genuine
dependency-bearing original polymorphic constant history. -/
theorem polymorphic_admitted :
    (admitSourceTypeInTheory DefinitionHistoryModels.Controls.polymorphicAliasResult.context
      polymorphicCertificates polymorphicRequest).isSome = true := by
  decide +kernel

def polymorphicResult : SourceTypeDefinitionResult :=
  (admitSourceTypeInTheory DefinitionHistoryModels.Controls.polymorphicAliasResult.context
    polymorphicCertificates polymorphicRequest).get polymorphic_admitted

theorem polymorphic_result_admitted :
    admitSourceTypeInTheory DefinitionHistoryModels.Controls.polymorphicAliasResult.context
      polymorphicCertificates polymorphicRequest = some polymorphicResult :=
  (Option.some_get polymorphic_admitted).symm

theorem polymorphic_parameter_arity : polymorphicRequest.typeVariables.length = 1 := by
  decide +kernel

/-- The exact stored source existence theorem has an original primitive
derivation. No model-truth premise or fabricated theorem record is used. -/
theorem polymorphic_existence_derived :
    Mettapedia.Logic.Derives (HOLLight.Rule emptyAxiomPolicy) polymorphicRequest.existence := by
  refine Mettapedia.Logic.Derives.node [] polymorphicExistence ?_ ?_
  · refine Or.inl ⟨.refl ModelInterpretation.Controls.polymorphicIdentityTerm, rfl, ?_⟩
    exact ⟨_, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩
  · intro premise member
    cases member

theorem polymorphic_existence_proven :
    HOL.ClosedTheorySet.Provable (definitionTheory DefinitionHistoryModels.Controls.polymorphicDefinitions)
      (TypeAdmission.admittedImage polymorphic_result_admitted).formula :=
  existence_proof_of_kernel_derives DefinitionHistoryModels.Controls.polymorphicDefinitions
    polymorphic_result_admitted polymorphic_existence_derived

theorem boolean_tuple_admitted (other : OperatorFamilies.{w}) :
    (family? DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other [proposition]).isSome = true := by
  simp [family?, polymorphic_parameter_arity]

theorem natural_tuple_admitted (other : OperatorFamilies.{w}) :
    (family? DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other [TypeFamilySemantics.Controls.natural]).isSome = true := by
  simp [family?, polymorphic_parameter_arity]

theorem missing_parameter_refused (other : OperatorFamilies.{w}) :
    family? DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other [] = none :=
  family?_wrong_arity _ _ _ _ [] (by simp [polymorphic_parameter_arity])

theorem excess_parameter_refused (other : OperatorFamilies.{w}) :
    family? DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other [proposition, TypeFamilySemantics.Controls.natural] = none :=
  family?_wrong_arity _ _ _ _ _ (by simp [polymorphic_parameter_arity])

theorem unused_parameter_absent : Name.global "unused" ∉ polymorphicRequest.typeVariables := by
  decide +kernel

/-- Changing an unused assignment cannot change the constructed subtype or
its canonical inhabitant. The actual witness still establishes nonemptiness. -/
theorem unused_parameter_preserves_domain (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (unused : Domain.{w}) :
    predicateDomain DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other (Function.update assignment (Name.global "unused") unused) =
    predicateDomain DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other assignment := by
  apply predicateDomain_assignment_agreement
  intro parameter member
  apply Function.update_of_ne
  intro equal
  exact unused_parameter_absent (equal ▸ member)

end Controls

end Mettapedia.Languages.HOLLight.UniformTypeDefinitionFamily
