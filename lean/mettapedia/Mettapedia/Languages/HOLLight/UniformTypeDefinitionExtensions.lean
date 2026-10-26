import Mettapedia.Languages.HOLLight.UniformTypeDefinitionInstances

/-!
# Fresh operator preservation of uniform witnessed source models

A subsequently fresh operator cannot occur in the original admitted
predicate or represented type. Their actual denotations preserve the
complete witnessed domain, including its selected inhabitant. Rebuilding
the installed source model therefore retains its original licensed values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.UniformTypeDefinitionExtensions

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters UniformTypeDefinitionFamily UniformTypeDefinitionModels

universe w

variable {initial context : TheoryContext}
  (history : DefinitionHistoryModels.ConstantHistory initial context)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w})
  (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
  (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
  (fresh : result.context.signature.typeOperators operator = none)

include accepted fresh in
/-- Exact original signature inclusion earns predecessor freshness. -/
theorem predecessor_fresh : context.signature.typeOperators operator = none := by
  cases registered : context.signature.typeOperators operator with
  | none => rfl
  | some arity =>
      have retained := (admitSourceTypeInTheory_result accepted).1.1 operator arity registered
      rw [fresh] at retained
      cases retained

include accepted fresh in
/-- The two complete operator identities are distinct by actual admission,
not merely because their displayed names differ. -/
theorem operators_distinct : operator ≠ SourceTypeDefinitionTransport.operator request := by
  intro same
  have retained : result.context.signature.typeOperators
      (SourceTypeDefinitionTransport.operator request) = some request.typeVariables.length := by
    rw [UniformTypeDefinitionInstances.source_signature accepted]
    simp [Signature.addConstant, Signature.addTypeOperator]
  rw [← same, fresh] at retained
  cases retained

include accepted notBool notFunction fresh in
/-- Formation of the original represented annotation excludes the later
operator throughout its complete carrier expression. -/
theorem representedCarrier_extend (assignment : Assignment.{w}) :
    HOL.Ty.denote.{0, w + 1}
      (priorModel history (extend other operator replacement) assignment).Carrier result.core.witness.ty.toHOL =
      HOL.Ty.denote.{0, w + 1} (priorModel history other assignment).Carrier result.core.witness.ty.toHOL := by
  rw [priorModel_carrier, priorModel_carrier]
  exact (evaluate_toHOL _ _ _).symm.trans
    ((congrArg Domain.Carrier (domain_extend_formed context.signature other operator replacement
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
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) :
    HEq (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
      (priorModel history (extend other operator replacement) assignment))
      (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
        (priorModel history other assignment)) := by
  have comparison := constantHistory_operator_agreement history functionArity other operator replacement
    notBool notFunction (predecessor_fresh accepted operator fresh) assignment
  change SourceAgreement context.signature
    (priorModel history (extend other operator replacement) assignment)
    (priorModel history other assignment) at comparison
  have carriers := representedCarrier_extend history accepted other operator replacement notBool notFunction fresh assignment
  apply down_function_heq carriers
  have values := comparison.denote (history.includes.1 TypeOp.function 2 functionArity)
    (priorModel_fullDomains history _ assignment) (priorModel_fullDomains history other assignment)
    (TypeAdmission.admittedImage accepted).predicateTranslated
    (admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1
    (by intro type member; cases member) (fun index => nomatch index) (fun index => nomatch index)
    (by intro type index; nomatch index)
  exact (heq_of_eq ((priorModel history (extend other operator replacement) assignment).denote_closed_valuation_eq
    (TypeAdmission.admittedImage accepted).predicateTerm _ _)).trans
    (values.trans (heq_of_eq ((priorModel history other assignment).denote_closed_valuation_eq
      (TypeAdmission.admittedImage accepted).predicateTerm _ _)))

include notBool notFunction fresh in
/-- The complete genuine subtype and its selected inhabitant survive a
fresh ambient extension, at every original parameter assignment. -/
theorem predicateDomain_extend
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) :
    predicateDomain history accepted proof (extend other operator replacement) assignment =
      predicateDomain history accepted proof other assignment := by
  apply inhabitedSubtype_congr
  · exact representedCarrier_extend history accepted other operator replacement notBool notFunction fresh assignment
  · exact representedPredicate_extend history accepted other operator replacement notBool notFunction fresh functionArity assignment

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
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) :
    HEq (abstraction history accepted proof (extend other operator replacement) assignment)
      (abstraction history accepted proof other assignment) := by
  unfold abstraction predicateDomain
  exact (subtype_maps_heq
    (representedCarrier_extend history accepted other operator replacement notBool notFunction fresh assignment)
    (representedPredicate_extend history accepted other operator replacement notBool notFunction fresh functionArity assignment)
    _ _).1

include notBool notFunction fresh in
/-- Representation remains the actual subtype projection across the later
fresh operator extension. -/
theorem representation_extend
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) :
    HEq (representation history accepted proof (extend other operator replacement) assignment)
      (representation history accepted proof other assignment) := by
  unfold representation predicateDomain
  exact (subtype_maps_heq
    (representedCarrier_extend history accepted other operator replacement notBool notFunction fresh assignment)
    (representedPredicate_extend history accepted other operator replacement notBool notFunction fresh functionArity assignment)
    ⟨⟨TypeAdmission.representedWitness (TypeAdmission.admittedImage accepted)
      (priorModel history (extend other operator replacement) assignment),
      TypeAdmission.witness_valid _ _ (existence_models history accepted proof (extend other operator replacement) assignment)⟩⟩
    ⟨⟨TypeAdmission.representedWitness (TypeAdmission.admittedImage accepted)
      (priorModel history other assignment),
      TypeAdmission.witness_valid _ _ (existence_models history accepted proof other assignment)⟩⟩).2

include notBool notFunction fresh in
/-- The original arity gate and every complete witnessed tuple are
preserved. Unlicensed arities retain their original refusal. -/
theorem family?_extend
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (arguments : List Domain.{w}) :
    family? history accepted proof (extend other operator replacement) arguments =
      family? history accepted proof other arguments := by
  unfold family?
  split
  · rw [predicateDomain_extend history accepted proof other operator replacement notBool notFunction fresh functionArity]
  · rfl

include notBool notFunction fresh in
theorem family_extend
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2) :
    family history accepted proof (extend other operator replacement) = family history accepted proof other := by
  funext arguments
  exact congrArg (fun value : Option Domain.{w} => value.getD proposition)
    (family?_extend history accepted proof other operator replacement notBool notFunction fresh functionArity arguments)


include notBool notFunction fresh in
/-- Rebuilding the prior definition's operator table computes exactly the
same actual family, then installs the independent later family. -/
theorem operators_extend
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2) :
    operators history accepted proof (extend other operator replacement) =
      extend (operators history accepted proof other) operator replacement := by
  unfold operators
  rw [family_extend history accepted proof other operator replacement notBool notFunction fresh functionArity]
  exact extend_commute other operator (SourceTypeDefinitionTransport.operator request) replacement _
    (operators_distinct accepted operator fresh)

include notBool notFunction fresh in
/-- Every original parameter field of a formed public carrier receives the
same complete domain under the fresh extension. -/
theorem instanceArguments_extend
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    instanceArguments history accepted proof (extend other operator replacement) assignment substitution =
      instanceArguments history accepted proof other assignment substitution := by
  simp only [SourceTypeDefinitionTransport.sourceCarrierType, TypeFormed] at formedCarrier
  simp only [instanceArguments]
  rw [operators_extend history accepted proof other operator replacement notBool notFunction fresh functionArity]
  apply List.map_congr_left
  intro parameter member
  exact domain_extend_formed result.context.signature (operators history accepted proof other)
    operator replacement notBool notFunction fresh assignment _
    (formedCarrier.2 _ (List.mem_map.mpr ⟨parameter, member, rfl⟩))

include notBool notFunction fresh in
/-- The actual transported installed abstraction agrees at every original
formed public source instance. -/
theorem abstractionInstance_extend
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (publicFormed : TypeFormed result.context.signature
      (abstractionAnnotation (request := request) (result := result) substitution)) :
    HEq (abstractionInstance history accepted proof (extend other operator replacement) assignment substitution)
      (abstractionInstance history accepted proof other assignment substitution) := by
  have arguments := instanceArguments_extend history accepted proof other operator replacement notBool notFunction fresh
    functionArity assignment substitution (publicFormed.function_components _).2
  have maps : HEq
      (abstraction history accepted proof (extend other operator replacement)
        (instanceAssignment history accepted proof (extend other operator replacement) assignment substitution))
      (abstraction history accepted proof other (instanceAssignment history accepted proof other assignment substitution)) := by
    unfold instanceAssignment
    rw [arguments]
    exact abstraction_extend history accepted proof other operator replacement notBool notFunction fresh functionArity _
  exact (abstractionInstance_heq history accepted proof (extend other operator replacement) assignment substitution).trans
    (maps.trans (abstractionInstance_heq history accepted proof other assignment substitution).symm)

include notBool notFunction fresh in
/-- The actual transported installed representation agrees at every
original formed public source instance. -/
theorem representationInstance_extend
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (publicFormed : TypeFormed result.context.signature
      (representationAnnotation (request := request) (result := result) substitution)) :
    HEq (representationInstance history accepted proof (extend other operator replacement) assignment substitution)
      (representationInstance history accepted proof other assignment substitution) := by
  have arguments := instanceArguments_extend history accepted proof other operator replacement notBool notFunction fresh
    functionArity assignment substitution (publicFormed.function_components _).1
  have maps : HEq
      (representation history accepted proof (extend other operator replacement)
        (instanceAssignment history accepted proof (extend other operator replacement) assignment substitution))
      (representation history accepted proof other (instanceAssignment history accepted proof other assignment substitution)) := by
    unfold instanceAssignment
    rw [arguments]
    exact representation_extend history accepted proof other operator replacement notBool notFunction fresh functionArity _
  exact (representationInstance_heq history accepted proof (extend other operator replacement) assignment substitution).trans
    (maps.trans (representationInstance_heq history accepted proof other assignment substitution).symm)

include notBool notFunction fresh in
/-- All previous original constant declarations preserve their actual
meanings, including instances at the current new type. -/
theorem carrierModel_extend_agreement
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) :
    SourceAgreement (comparisonSignature (context := context) (result := result))
      (carrierModel history accepted proof (extend other operator replacement) assignment)
      (carrierModel history accepted proof other assignment) := by
  change SourceAgreement (ConstantHistoryExpandedTypes.withTypes context.signature result.context.signature)
    (history.extendModel (initialModel (operators history accepted proof (extend other operator replacement)) assignment))
    (history.extendModel (initialModel (operators history accepted proof other) assignment))
  rw [operators_extend history accepted proof other operator replacement notBool notFunction fresh functionArity]
  exact ConstantHistoryExpandedTypes.history_agreement history result.context.signature
    (fun candidate arity registered => (admitSourceTypeInTheory_result accepted).1.1 candidate arity
      (history.includes.1 candidate arity registered)) functionArity
    (initial_operator_agreement (ConstantHistoryExpandedTypes.withTypes initial.signature result.context.signature)
      (operators history accepted proof other) operator replacement notBool notFunction fresh assignment)
    (initialModel_fullDomains _ _) (initialModel_fullDomains _ _)

include notBool notFunction fresh in
/-- The entire original installed successor model preserves licensed
carriers, constants and free source variables under a later fresh operator. -/
theorem model_extend_agreement
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) :
    SourceAgreement result.context.signature
      (model history accepted proof (extend other operator replacement) assignment)
      (model history accepted proof other assignment) := by
  have predecessor := carrierModel_extend_agreement history accepted proof other operator replacement
    notBool notFunction fresh functionArity assignment
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    rw [UniformTypeDefinitionSupport.model_carrier_eq_atomic, UniformTypeDefinitionSupport.model_carrier_eq_atomic,
      operators_extend history accepted proof other operator replacement notBool notFunction fresh functionArity]
    have domains := domain_extend_formed result.context.signature (operators history accepted proof other)
      operator replacement notBool notFunction fresh assignment (Ty.fromHOL type) formed
    simpa only [Ty.toHOL_fromHOL] using (evaluate_toHOL _ _ _).symm.trans
      ((congrArg Domain.Carrier domains).trans (evaluate_toHOL _ _ _))
  · intro constant annotation type typed formed declared
    by_cases abstractionName : constant = result.output.abstractionConstant
    · subst constant
      obtain ⟨substitution, rfl⟩ := UniformTypeDefinitionInstances.licensed_abstraction_instance accepted declared
      cases typed
      exact (heq_of_eq (meanings_abstraction history accepted proof (extend other operator replacement) assignment substitution)).trans
        ((abstractionInstance_extend history accepted proof other operator replacement notBool notFunction fresh
          functionArity assignment substitution formed).trans
          (heq_of_eq (meanings_abstraction history accepted proof other assignment substitution)).symm)
    · by_cases representationName : constant = result.output.representationConstant
      · subst constant
        obtain ⟨substitution, rfl⟩ := UniformTypeDefinitionInstances.licensed_representation_instance accepted declared
        cases typed
        exact (heq_of_eq (meanings_representation history accepted proof (extend other operator replacement) assignment substitution)).trans
          ((representationInstance_extend history accepted proof other operator replacement notBool notFunction fresh
            functionArity assignment substitution formed).trans
            (heq_of_eq (meanings_representation history accepted proof other assignment substitution)).symm)
      · rw [meanings_other history accepted proof (extend other operator replacement) assignment typed abstractionName representationName,
          meanings_other history accepted proof other assignment typed abstractionName representationName]
        exact predecessor.constants constant annotation typed
          ((typeFormed_eq_of_operators result.context.signature
            (comparisonSignature (context := context) (result := result)) rfl annotation).mp formed)
          (UniformTypeDefinitionInstances.old_constant_instance accepted abstractionName representationName declared)
  · intro sourceVar type typed formed
    rw [meanings_variable history accepted proof (extend other operator replacement) assignment sourceVar typed,
      meanings_variable history accepted proof other assignment sourceVar typed]
    exact predecessor.variableValues sourceVar typed
      ((typeFormed_eq_of_operators result.context.signature
        (comparisonSignature (context := context) (result := result)) rfl sourceVar.ty).mp formed)

include notBool notFunction fresh in
/-- Every old formed source sentence retains truth in the rebuilt uniform
model. The comparison uses its original source translation and licences. -/
theorem model_models_extend
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w})
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed result.context.signature term) :
    (model history accepted proof (extend other operator replacement) assignment).models formula ↔
      (model history accepted proof other assignment).models formula :=
  (model_extend_agreement history accepted proof other operator replacement notBool notFunction fresh
    functionArity assignment).models
    ((admitSourceTypeInTheory_result accepted).1.1 TypeOp.function 2
      (history.includes.1 TypeOp.function 2 functionArity))
    (model_fullDomains history accepted proof _ assignment) (model_fullDomains history accepted proof other assignment)
    translation formed

include notBool notFunction fresh in
/-- The earned fresh-operator comparison persists through any following
original admitted constant history, retaining every source declaration. -/
theorem constant_suffix_extend_agreement {final : TheoryContext}
    (suffix : DefinitionHistoryModels.ConstantHistory result.context final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w}) :
    SourceAgreement final.signature
      (suffix.extendModel (model history accepted proof (extend other operator replacement) assignment))
      (suffix.extendModel (model history accepted proof other assignment)) :=
  (model_extend_agreement history accepted proof other operator replacement notBool notFunction fresh
    functionArity assignment).constantHistory suffix
    ((admitSourceTypeInTheory_result accepted).1.1 TypeOp.function 2
      (history.includes.1 TypeOp.function 2 functionArity))
    (model_fullDomains history accepted proof _ assignment) (model_fullDomains history accepted proof other assignment)

include notBool notFunction fresh in
theorem constant_suffix_models_extend {final : TheoryContext}
    (suffix : DefinitionHistoryModels.ConstantHistory result.context final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (assignment : Assignment.{w})
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed final.signature term) :
    (suffix.extendModel (model history accepted proof (extend other operator replacement) assignment)).models formula ↔
      (suffix.extendModel (model history accepted proof other assignment)).models formula :=
  (constant_suffix_extend_agreement history accepted proof other operator replacement notBool notFunction fresh
    suffix functionArity assignment).models
    (suffix.includes.1 TypeOp.function 2 ((admitSourceTypeInTheory_result accepted).1.1 TypeOp.function 2
      (history.includes.1 TypeOp.function 2 functionArity)))
    (suffix.fullDomains _ (model_fullDomains history accepted proof _ assignment))
    (suffix.fullDomains _ (model_fullDomains history accepted proof other assignment)) translation formed

namespace Controls

open UniformTypeDefinitionFamily.Controls DefinitionAdapters.ContextControls

def laterOperator : TypeOp := .mk (Name.global "LaterScalar") .undefined

theorem later_operator_fresh : polymorphicResult.context.signature.typeOperators laterOperator = none := by
  decide +kernel

theorem later_operator_nonprimitive : laterOperator ≠ TypeOp.bool ∧ laterOperator ≠ TypeOp.function := by
  constructor
  · intro same
    have recognized := (TypeOp.same_eq_true_iff laterOperator TypeOp.bool).mpr same
    have different : laterOperator.same TypeOp.bool = false := by decide +kernel
    rw [different] at recognized
    cases recognized
  · intro same
    have recognized := (TypeOp.same_eq_true_iff laterOperator TypeOp.function).mpr same
    have different : laterOperator.same TypeOp.function = false := by decide +kernel
    rw [different] at recognized
    cases recognized

/-- One genuinely constructed original family keeps every complete domain
value, including its inhabitant, for arbitrary later operator meanings. -/
theorem original_family_preserved (other : OperatorFamilies.{w})
    (replacement : List Domain.{w} → Domain.{w}) (arguments : List Domain.{w}) :
    family? DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven (extend other laterOperator replacement) arguments =
      family? DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
        polymorphic_existence_proven other arguments :=
  family?_extend _ polymorphic_result_admitted polymorphic_existence_proven other laterOperator replacement
    later_operator_nonprimitive.1 later_operator_nonprimitive.2 later_operator_fresh
    (core_includes.1 TypeOp.function 2 function_registered) arguments

/-- Both actual installed source symbols keep their original values after
an arbitrary family is installed at the later fresh identity. -/
theorem original_maps_preserved (other : OperatorFamilies.{w})
    (replacement : List Domain.{w} → Domain.{w}) (assignment : Assignment.{w}) :
    let originalHistory := DefinitionHistoryModels.Controls.polymorphicDefinitions
    HEq ((model originalHistory polymorphic_result_admitted polymorphic_existence_proven
      (extend other laterOperator replacement) assignment).constDen
      (.constant polymorphicResult.output.abstractionConstant
        (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl))
      ((model originalHistory polymorphic_result_admitted polymorphic_existence_proven other assignment).constDen
        (.constant polymorphicResult.output.abstractionConstant
          (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl)) ∧
    HEq ((model originalHistory polymorphic_result_admitted polymorphic_existence_proven
      (extend other laterOperator replacement) assignment).constDen
      (.constant polymorphicResult.output.representationConstant
        (representationAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl))
      ((model originalHistory polymorphic_result_admitted polymorphic_existence_proven other assignment).constDen
        (.constant polymorphicResult.output.representationConstant
          (representationAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl)) := by
  intro originalHistory
  have compared := model_extend_agreement originalHistory polymorphic_result_admitted polymorphic_existence_proven
    other laterOperator replacement later_operator_nonprimitive.1 later_operator_nonprimitive.2 later_operator_fresh
    (core_includes.1 TypeOp.function 2 function_registered) assignment
  exact ⟨compared.constants _ _ rfl UniformTypeDefinitionInstances.Controls.original_abstraction_schema_formed
      (UniformTypeDefinitionInstances.abstraction_registered_instance polymorphic_result_admitted TypeSubst.empty),
    compared.constants _ _ rfl UniformTypeDefinitionInstances.Controls.original_representation_schema_formed
      (UniformTypeDefinitionInstances.representation_registered_instance polymorphic_result_admitted TypeSubst.empty)⟩

/-- The original dependency-bearing alias is preserved at the already new
carrier instance, beyond its original predecessor's formation scope. -/
theorem original_alias_new_carrier_preserved (other : OperatorFamilies.{w})
    (replacement : List Domain.{w} → Domain.{w}) (assignment : Assignment.{w}) :
    let originalHistory := DefinitionHistoryModels.Controls.polymorphicDefinitions
    HEq ((model originalHistory polymorphic_result_admitted polymorphic_existence_proven
      (extend other laterOperator replacement) assignment).constDen
      (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
        ConstantHistoryExpandedTypes.Controls.aliasNewCarrierAnnotation rfl))
      ((model originalHistory polymorphic_result_admitted polymorphic_existence_proven other assignment).constDen
        (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
          ConstantHistoryExpandedTypes.Controls.aliasNewCarrierAnnotation rfl)) := by
  intro originalHistory
  have compared := model_extend_agreement originalHistory polymorphic_result_admitted polymorphic_existence_proven
    other laterOperator replacement later_operator_nonprimitive.1 later_operator_nonprimitive.2 later_operator_fresh
    (core_includes.1 TypeOp.function 2 function_registered) assignment
  apply compared.constants _ _ rfl
  · exact (typeFormed_eq_of_operators
      (ConstantHistoryExpandedTypes.withTypes DefinitionHistoryModels.Controls.polymorphicAliasResult.context.signature
        polymorphicResult.context.signature) polymorphicResult.context.signature rfl _).mp
      ConstantHistoryExpandedTypes.Controls.alias_new_carrier_formed
  · exact ConstantHistoryExpandedTypes.Controls.alias_new_carrier_original_instance.mono
      (admitSourceTypeInTheory_result polymorphic_result_admitted).1

/-- Total ambient model data never licences an undeclared old source type. -/
theorem later_raw_type_not_previously_formed :
    typeFormedB polymorphicResult.context.signature (.op laterOperator []) = false := by
  decide +kernel

theorem later_raw_type_formed_after_registration :
    typeFormedB (polymorphicResult.context.signature.addTypeOperator laterOperator 0) (.op laterOperator []) = true := by
  decide +kernel

/-- The genuine family still refuses the original wrong number of type
parameters after the independent ambient extension. -/
theorem original_wrong_arity_refused (other : OperatorFamilies.{w})
    (replacement : List Domain.{w} → Domain.{w}) :
    family? DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven (extend other laterOperator replacement) [] = none :=
  family?_wrong_arity _ polymorphic_result_admitted polymorphic_existence_proven _ _ (by decide +kernel)

end Controls

end Mettapedia.Languages.HOLLight.UniformTypeDefinitionExtensions
