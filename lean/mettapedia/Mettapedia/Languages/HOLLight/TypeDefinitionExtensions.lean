import Mettapedia.Languages.HOLLight.TypeDefinitionModels
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionExtensions

/-!
# Fresh ambient operators after actual mixed witnessed definitions

The installed source interpretation retains every original licensed carrier
and symbol after a later fresh ambient family. These laws close the semantic
construction state needed by the original chronological mixed recurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.TypeDefinitionExtensions

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters DefinitionModelFamily
open DefinitionModelFamily.Witnessed TypeDefinitionModels
open UniformTypeDefinitionModels (abstractionAnnotation representationAnnotation comparisonSignature)
open UniformTypeDefinitionFamily (inhabitedSubtype inhabitedSubtype_congr)
open UniformTypeDefinitionExtensions (predecessor_fresh operators_distinct)

universe w

variable {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol} (prior : Family.{w} initial context theory)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (theory) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w}) (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
  (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
  (fresh : result.context.signature.typeOperators operator = none)

include accepted notBool notFunction fresh in
/-- Formation of the original represented annotation excludes the later
operator throughout its complete carrier expression. -/
theorem representedCarrier_extend (assignment : Assignment.{w}) :
    HOL.Ty.denote.{0, w + 1}
      (prior.model (extend other operator replacement) assignment).Carrier result.core.witness.ty.toHOL =
      HOL.Ty.denote.{0, w + 1} (prior.model other assignment).Carrier result.core.witness.ty.toHOL := by
  rw [prior.carrier, prior.carrier, prior.freshOperators other operator replacement notBool notFunction (predecessor_fresh accepted operator fresh)]
  exact (evaluate_toHOL _ _ _).symm.trans
    ((congrArg Domain.Carrier (domain_extend_formed context.signature (prior.operators other) operator replacement
      notBool notFunction (predecessor_fresh accepted operator fresh) assignment result.core.witness.ty
      (SourceTypeDefinitionTransport.admitted_represented_formed accepted))).trans (evaluate_toHOL _ _ _))

private theorem down_function_heq {firstCarrier secondCarrier : Type (w + 1)}
    (carriers : firstCarrier = secondCarrier)
    {first : firstCarrier → ULift.{w + 1, 0} Prop}
    {second : secondCarrier → ULift.{w + 1, 0} Prop}
    (functions : HEq first second) :
    HEq (fun value => (first value).down) (fun value => (second value).down) := by
  cases carriers
  exact heq_of_eq (congrArg (fun function => fun value => (function value).down) (eq_of_heq functions))

include notBool notFunction fresh in
/-- The exact retained predicate follows the actual predecessor history
when a later fresh operator is installed in its ambient table. -/
theorem representedPredicate_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    HEq (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
      (prior.model (extend other operator replacement) assignment))
      (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
        (prior.model other assignment)) := by
  have comparison := prior.freshModels other operator replacement
    notBool notFunction (predecessor_fresh accepted operator fresh) assignment
  change SourceAgreement context.signature
    (prior.model (extend other operator replacement) assignment)
    (prior.model other assignment) at comparison
  have carriers := representedCarrier_extend prior accepted other operator replacement notBool notFunction fresh assignment
  apply down_function_heq carriers
  have values := comparison.denote (prior.includes.1 TypeOp.function 2 primitives.functionArity)
    (prior.fullDomains _ assignment) (prior.fullDomains other assignment)
    (TypeAdmission.admittedImage accepted).predicateTranslated
    (admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1
    (by intro type member; cases member) (fun index => nomatch index) (fun index => nomatch index)
    (by intro type index; nomatch index)
  exact (heq_of_eq ((prior.model (extend other operator replacement) assignment).denote_closed_valuation_eq
    (TypeAdmission.admittedImage accepted).predicateTerm _ _)).trans
    (values.trans (heq_of_eq ((prior.model other assignment).denote_closed_valuation_eq
      (TypeAdmission.admittedImage accepted).predicateTerm _ _)))

include notBool notFunction fresh in
/-- The complete genuine subtype and its selected inhabitant survive a
fresh ambient extension, at every original parameter assignment. -/
theorem predicateDomain_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    predicateDomain prior accepted proof (extend other operator replacement) assignment =
      predicateDomain prior accepted proof other assignment := by
  apply inhabitedSubtype_congr
  · exact representedCarrier_extend prior accepted other operator replacement notBool notFunction fresh assignment
  · exact representedPredicate_extend prior accepted other operator replacement notBool notFunction fresh primitives assignment

private theorem subtype_maps_heq {firstCarrier secondCarrier : Type (w + 1)}
    (carriers : firstCarrier = secondCarrier)
    {firstPredicate : firstCarrier → Prop} {secondPredicate : secondCarrier → Prop}
    (predicates : HEq firstPredicate secondPredicate)
    (firstNonempty : Nonempty {value // firstPredicate value})
    (secondNonempty : Nonempty {value // secondPredicate value}) :
    HEq (HOL.WitnessedTypeDefinition.abstraction firstPredicate
      (inhabitedSubtype firstCarrier firstPredicate firstNonempty).inhabitant.val
      (inhabitedSubtype firstCarrier firstPredicate firstNonempty).inhabitant.property)
      (HOL.WitnessedTypeDefinition.abstraction secondPredicate
        (inhabitedSubtype secondCarrier secondPredicate secondNonempty).inhabitant.val
        (inhabitedSubtype secondCarrier secondPredicate secondNonempty).inhabitant.property) ∧
    HEq (@HOL.WitnessedTypeDefinition.representation firstCarrier firstPredicate)
      (@HOL.WitnessedTypeDefinition.representation secondCarrier secondPredicate) := by
  cases carriers
  have same := eq_of_heq predicates
  subst secondPredicate
  exact ⟨HEq.rfl, HEq.rfl⟩

include notBool notFunction fresh in
/-- Abstraction retains its actual outside-predicate behavior and canonical
valid fallback value across the later fresh operator extension. -/
theorem abstraction_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    HEq (abstraction prior accepted proof (extend other operator replacement) assignment)
      (abstraction prior accepted proof other assignment) := by
  unfold abstraction predicateDomain
  exact (subtype_maps_heq
    (representedCarrier_extend prior accepted other operator replacement notBool notFunction fresh assignment)
    (representedPredicate_extend prior accepted other operator replacement notBool notFunction fresh primitives assignment)
    _ _).1

include notBool notFunction fresh in
/-- Representation remains the actual subtype projection across the later
fresh operator extension. -/
theorem representation_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    HEq (representation prior accepted proof (extend other operator replacement) assignment)
      (representation prior accepted proof other assignment) := by
  unfold representation predicateDomain
  exact (subtype_maps_heq
    (representedCarrier_extend prior accepted other operator replacement notBool notFunction fresh assignment)
    (representedPredicate_extend prior accepted other operator replacement notBool notFunction fresh primitives assignment)
    ⟨⟨TypeAdmission.representedWitness (TypeAdmission.admittedImage accepted)
      (prior.model (extend other operator replacement) assignment),
      TypeAdmission.witness_valid _ _ (existence_models prior accepted proof (extend other operator replacement) assignment)⟩⟩
    ⟨⟨TypeAdmission.representedWitness (TypeAdmission.admittedImage accepted)
      (prior.model other assignment),
      TypeAdmission.witness_valid _ _ (existence_models prior accepted proof other assignment)⟩⟩).2


private theorem extend_commute (original : OperatorFamilies.{w}) (first second : TypeOp)
    (firstFamily secondFamily : List Domain.{w} → Domain.{w}) (different : first ≠ second) :
    extend (extend original first firstFamily) second secondFamily =
      extend (extend original second secondFamily) first firstFamily := by
  funext candidate arguments
  by_cases firstMatch : candidate = first
  · subst candidate
    simp [extend, different]
  · by_cases secondMatch : candidate = second
    · subst candidate
      simp [extend, Ne.symm different]
    · simp [extend, firstMatch, secondMatch]


include notBool notFunction fresh in
/-- Rebuilding the actual preceding mixed operator table and installing the
new family commutes with a later unrelated admitted-family extension. -/
theorem operators_extend (primitives : Primitives initial) :
    operators prior accepted proof (extend other operator replacement) =
      extend (operators prior accepted proof other) operator replacement := by
  unfold Witnessed.operators
  rw [prior.freshOperators other operator replacement notBool notFunction (predecessor_fresh accepted operator fresh)]
  rw [Witnessed.family_extend prior accepted proof other primitives operator replacement notBool notFunction
    (predecessor_fresh accepted operator fresh)]
  exact extend_commute (prior.operators other) operator (SourceTypeDefinitionTransport.operator request) replacement _
    (operators_distinct accepted operator fresh)

include notBool notFunction fresh in
/-- Every original parameter field of a formed public carrier receives the
same complete domain under the fresh extension. -/
theorem instanceArguments_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    instanceArguments prior accepted proof (extend other operator replacement) assignment substitution =
      instanceArguments prior accepted proof other assignment substitution := by
  simp only [SourceTypeDefinitionTransport.sourceCarrierType, TypeFormed] at formedCarrier
  simp only [instanceArguments]
  rw [operators_extend prior accepted proof other operator replacement notBool notFunction fresh primitives]
  apply List.map_congr_left
  intro parameter member
  exact domain_extend_formed result.context.signature (operators prior accepted proof other)
    operator replacement notBool notFunction fresh assignment _
    (formedCarrier.2 _ (List.mem_map.mpr ⟨parameter, member, rfl⟩))

include notBool notFunction fresh in
/-- The actual transported installed abstraction agrees at every original
formed public source instance. -/
theorem abstractionInstance_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (publicFormed : TypeFormed result.context.signature
      (abstractionAnnotation (request := request) (result := result) substitution)) :
    HEq (abstractionInstance prior accepted proof (extend other operator replacement) assignment substitution)
      (abstractionInstance prior accepted proof other assignment substitution) := by
  have arguments := instanceArguments_extend prior accepted proof other operator replacement notBool notFunction fresh
    primitives assignment substitution (publicFormed.function_components _).2
  have maps : HEq
      (abstraction prior accepted proof (extend other operator replacement)
        (instanceAssignment prior accepted proof (extend other operator replacement) assignment substitution))
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other assignment substitution)) := by
    unfold instanceAssignment
    rw [arguments]
    exact abstraction_extend prior accepted proof other operator replacement notBool notFunction fresh primitives _
  exact (abstractionInstance_heq prior accepted proof (extend other operator replacement) assignment substitution).trans
    (maps.trans (abstractionInstance_heq prior accepted proof other assignment substitution).symm)

include notBool notFunction fresh in
/-- The actual transported installed representation agrees at every
original formed public source instance. -/
theorem representationInstance_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (publicFormed : TypeFormed result.context.signature
      (representationAnnotation (request := request) (result := result) substitution)) :
    HEq (representationInstance prior accepted proof (extend other operator replacement) assignment substitution)
      (representationInstance prior accepted proof other assignment substitution) := by
  have arguments := instanceArguments_extend prior accepted proof other operator replacement notBool notFunction fresh
    primitives assignment substitution (publicFormed.function_components _).1
  have maps : HEq
      (representation prior accepted proof (extend other operator replacement)
        (instanceAssignment prior accepted proof (extend other operator replacement) assignment substitution))
      (representation prior accepted proof other (instanceAssignment prior accepted proof other assignment substitution)) := by
    unfold instanceAssignment
    rw [arguments]
    exact representation_extend prior accepted proof other operator replacement notBool notFunction fresh primitives _
  exact (representationInstance_heq prior accepted proof (extend other operator replacement) assignment substitution).trans
    (maps.trans (representationInstance_heq prior accepted proof other assignment substitution).symm)


include notBool notFunction fresh in
/-- The actual previous mixed construction retains old declarations at
all types formed in the newly extended registry. -/
theorem carrierModel_extend_agreement (primitives : Primitives initial) (assignment : Assignment.{w}) :
    SourceAgreement (comparisonSignature (context := context) (result := result))
      (carrierModel prior accepted proof (extend other operator replacement) assignment)
      (carrierModel prior accepted proof other assignment) := by
  unfold Witnessed.carrierModel
  rw [Witnessed.family_extend prior accepted proof other primitives operator replacement notBool notFunction
    (predecessor_fresh accepted operator fresh)]
  rw [extend_commute other operator (SourceTypeDefinitionTransport.operator request) replacement _
    (operators_distinct accepted operator fresh)]
  exact prior.freshModels_withTypes
    (extend other (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)) result.context.signature
    (admitSourceTypeInTheory_result accepted).1.1 operator replacement notBool notFunction fresh assignment

include notBool notFunction fresh in
/-- The entire original installed successor model preserves licensed
carriers, constants and free source variables under a later fresh operator. -/
theorem model_extend_agreement
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    SourceAgreement result.context.signature
      (model prior accepted proof (extend other operator replacement) assignment)
      (model prior accepted proof other assignment) := by
  have predecessor := carrierModel_extend_agreement prior accepted proof other operator replacement
    notBool notFunction fresh primitives assignment
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    rw [TypeDefinitionModels.model_carrier_eq_atomic, TypeDefinitionModels.model_carrier_eq_atomic,
      operators_extend prior accepted proof other operator replacement notBool notFunction fresh primitives]
    have domains := domain_extend_formed result.context.signature (operators prior accepted proof other)
      operator replacement notBool notFunction fresh assignment (Ty.fromHOL type) formed
    simpa only [Ty.toHOL_fromHOL] using (evaluate_toHOL _ _ _).symm.trans
      ((congrArg Domain.Carrier domains).trans (evaluate_toHOL _ _ _))
  · intro constant annotation type typed formed declared
    by_cases abstractionName : constant = result.output.abstractionConstant
    · subst constant
      obtain ⟨substitution, rfl⟩ := UniformTypeDefinitionInstances.licensed_abstraction_instance accepted declared
      cases typed
      exact (heq_of_eq (meanings_abstraction prior accepted proof (extend other operator replacement) assignment substitution)).trans
        ((abstractionInstance_extend prior accepted proof other operator replacement notBool notFunction fresh
          primitives assignment substitution formed).trans
          (heq_of_eq (meanings_abstraction prior accepted proof other assignment substitution)).symm)
    · by_cases representationName : constant = result.output.representationConstant
      · subst constant
        obtain ⟨substitution, rfl⟩ := UniformTypeDefinitionInstances.licensed_representation_instance accepted declared
        cases typed
        exact (heq_of_eq (meanings_representation prior accepted proof (extend other operator replacement) assignment substitution)).trans
          ((representationInstance_extend prior accepted proof other operator replacement notBool notFunction fresh
            primitives assignment substitution formed).trans
            (heq_of_eq (meanings_representation prior accepted proof other assignment substitution)).symm)
      · rw [meanings_other prior accepted proof (extend other operator replacement) assignment typed abstractionName representationName,
          meanings_other prior accepted proof other assignment typed abstractionName representationName]
        exact predecessor.constants constant annotation typed
          ((typeFormed_eq_of_operators result.context.signature
            (comparisonSignature (context := context) (result := result)) rfl annotation).mp formed)
          (UniformTypeDefinitionInstances.old_constant_instance accepted abstractionName representationName declared)
  · intro sourceVar type typed formed
    rw [meanings_variable prior accepted proof (extend other operator replacement) assignment sourceVar typed,
      meanings_variable prior accepted proof other assignment sourceVar typed]
    exact predecessor.variableValues sourceVar typed
      ((typeFormed_eq_of_operators result.context.signature
        (comparisonSignature (context := context) (result := result)) rfl sourceVar.ty).mp formed)


end Mettapedia.Languages.HOLLight.TypeDefinitionExtensions
