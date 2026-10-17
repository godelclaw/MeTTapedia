import Mettapedia.Languages.HOLLight.UniformTypeDefinitionModels

/-!
# Earned support of uniform source type-definition meanings

The installed source abstraction and representation depend on the complete
domains of their public type arguments. Agreement on the original annotation
support therefore preserves their values. This extends the actual predecessor
history's support theorem, rather than assuming model locality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.UniformTypeDefinitionSupport

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

theorem instanceArguments_assignment_agreement (first second : Assignment.{w}) (substitution : TypeSubst)
    (agree : ∀ parameter ∈ (SourceTypeDefinitionTransport.sourceCarrierType request substitution).typeVariables,
      first parameter = second parameter) :
    instanceArguments history accepted proof other first substitution =
      instanceArguments history accepted proof other second substitution := by
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
    HEq (abstractionInstance history accepted proof other first substitution)
      (abstractionInstance history accepted proof other second substitution) := by
  have arguments := instanceArguments_assignment_agreement history accepted proof other first second substitution
    (by
      intro parameter occurs
      apply agree parameter
      simp only [abstractionAnnotation, Ty.function, Ty.typeVariables, Ty.typeVariablesList,
        Finset.union_empty, Finset.mem_union]
      exact Or.inr occurs)
  have maps : HEq
      (abstraction history accepted proof other (instanceAssignment history accepted proof other first substitution))
      (abstraction history accepted proof other (instanceAssignment history accepted proof other second substitution)) := by
    unfold instanceAssignment
    rw [arguments]
  exact (abstractionInstance_heq history accepted proof other first substitution).trans
    (maps.trans (abstractionInstance_heq history accepted proof other second substitution).symm)

theorem representation_assignment_agreement (first second : Assignment.{w}) (substitution : TypeSubst)
    (agree : ∀ parameter ∈ (representationAnnotation (request := request) (result := result) substitution).typeVariables,
      first parameter = second parameter) :
    HEq (representationInstance history accepted proof other first substitution)
      (representationInstance history accepted proof other second substitution) := by
  have arguments := instanceArguments_assignment_agreement history accepted proof other first second substitution
    (by
      intro parameter occurs
      apply agree parameter
      simp only [representationAnnotation, Ty.function, Ty.typeVariables, Ty.typeVariablesList,
        Finset.union_empty, Finset.mem_union]
      exact Or.inl occurs)
  have maps : HEq
      (representation history accepted proof other (instanceAssignment history accepted proof other first substitution))
      (representation history accepted proof other (instanceAssignment history accepted proof other second substitution)) := by
    unfold instanceAssignment
    rw [arguments]
  exact (representationInstance_heq history accepted proof other first substitution).trans
    (maps.trans (representationInstance_heq history accepted proof other second substitution).symm)

theorem model_carrier_eq_atomic (assignment : Assignment.{w}) :
    (model history accepted proof other assignment).Carrier =
      atomicCarrier (operators history accepted proof other) assignment := by
  rw [model_carrier, carrierModel, priorModel_carrier]
  rfl

theorem model_symbol_local : ModelAssignmentSupport.SymbolLocal (model history accepted proof other) := by
  intro first second type symbol agree
  have predecessor := history_initial_symbol_local history (operators history accepted proof other)
  cases symbol with
  | «variable» sourceVar typed =>
      rw [meanings_variable, meanings_variable]
      exact predecessor first second (.variable sourceVar typed) agree
  | constant constant annotation typed =>
      cases typed
      classical
      simp only [UniformTypeDefinitionModels.model, HOL.HenkinModel.standard, meanings]
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
            ((abstraction_assignment_agreement history accepted proof other first second declared.choose supported).trans
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
              ((representation_assignment_agreement history accepted proof other first second declared.choose supported).trans
                (eqRec_heq _ _).symm)
          · exact predecessor first second (.constant constant annotation rfl) agree
        · exact predecessor first second (.constant constant annotation rfl) agree

/-- Actual source denotation in the installed family has the support of
its original term and bound context. The symbol law is earned above. -/
theorem model_denote_parameter_agreement (first second : Assignment.{w})
    {bound : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol bound type}
    (translation : TranslatesCompositionally bound term type target)
    (termAgreement : ∀ name ∈ term.typeVariables, first name = second name)
    (contextAgreement : ∀ name ∈ ModelAssignmentSupport.contextSupport bound,
      first name = second name)
    (firstValuation : (model history accepted proof other first).Valuation bound)
    (secondValuation : (model history accepted proof other second).Valuation bound)
    (same : ∀ type (index : HOL.Var bound type), HEq (firstValuation index) (secondValuation index)) :
    HEq ((model history accepted proof other first).denote target firstValuation)
      ((model history accepted proof other second).denote target secondValuation) :=
  ModelAssignmentSupport.denote_parameter_agreement (operators history accepted proof other)
    (model history accepted proof other) (model_carrier_eq_atomic history accepted proof other)
    (model_fullDomains history accepted proof other) (model_symbol_local history accepted proof other)
    first second translation termAgreement contextAgreement firstValuation secondValuation same

/-- The truth of original closed source formulas ignores unused assignment
slots after the genuine uniform type extension. -/
theorem model_models_parameter_agreement (first second : Assignment.{w})
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (agree : ∀ name ∈ term.typeVariables, first name = second name) :
    (model history accepted proof other first).models formula ↔
      (model history accepted proof other second).models formula := by
  change ((model history accepted proof other first).denote formula _).down ↔
    ((model history accepted proof other second).denote formula _).down
  apply iff_of_eq
  apply congrArg (fun value : ULift.{w + 1, 0} Prop => value.down)
  apply eq_of_heq
  apply model_denote_parameter_agreement history accepted proof other first second translation agree
  · intro name member
    simp only [ModelAssignmentSupport.contextSupport, List.map_nil, Ty.typeVariablesList, Finset.notMem_empty] at member
  · intro type index
    nomatch index

/-- Every further original admitted constant declaration retains earned
support, including arbitrary dependency-bearing chronological suffixes. -/
theorem constant_suffix_symbol_local {final : TheoryContext}
    (suffix : DefinitionHistoryModels.ConstantHistory result.context final) :
    ModelAssignmentSupport.SymbolLocal
      (fun assignment => suffix.extendModel (model history accepted proof other assignment)) :=
  ModelAssignmentSupport.history_symbol_local suffix (operators history accepted proof other)
    (model history accepted proof other) (model_carrier_eq_atomic history accepted proof other)
    (model_fullDomains history accepted proof other) (model_symbol_local history accepted proof other)

/-- Old formed source sentences survive the entire following original
constant history. The preservation law uses every admitted step. -/
theorem constant_suffix_models_old {final : TheoryContext}
    (suffix : DefinitionHistoryModels.ConstantHistory result.context final) (assignment : Assignment.{w})
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (formed : AnnotationsFormed result.context.signature term)
    (translation : TranslatesCompositionally [] term .prop formula) :
    (suffix.extendModel (model history accepted proof other assignment)).models formula ↔
      (model history accepted proof other assignment).models formula :=
  suffix.models_old _ formed translation

namespace Controls

open UniformTypeDefinitionFamily.Controls

theorem original_parameter_table :
    polymorphicRequest.typeVariables = [TypeFamilySemantics.Controls.alpha] := by
  decide +kernel

/-- Both installed source symbols at a closed Boolean instance ignore all
assignment slots, including changes to domain inhabitants. -/
theorem closed_boolean_symbols_ignore_assignments (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) :
    HEq ((model DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other first).constDen
      (.constant polymorphicResult.output.abstractionConstant
        (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult)
          UniformTypeDefinitionModels.Controls.booleanInstance) rfl))
      ((model DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
        polymorphic_existence_proven other second).constDen
        (.constant polymorphicResult.output.abstractionConstant
          (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult)
            UniformTypeDefinitionModels.Controls.booleanInstance) rfl)) ∧
    HEq ((model DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other first).constDen
      (.constant polymorphicResult.output.representationConstant
        (representationAnnotation (request := polymorphicRequest) (result := polymorphicResult)
          UniformTypeDefinitionModels.Controls.booleanInstance) rfl))
      ((model DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
        polymorphic_existence_proven other second).constDen
        (.constant polymorphicResult.output.representationConstant
          (representationAnnotation (request := polymorphicRequest) (result := polymorphicResult)
            UniformTypeDefinitionModels.Controls.booleanInstance) rfl)) := by
  have abstractionClosed :
      (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult)
        UniformTypeDefinitionModels.Controls.booleanInstance).typeVariables = ∅ := by
    decide +kernel
  have representationClosed :
      (representationAnnotation (request := polymorphicRequest) (result := polymorphicResult)
        UniformTypeDefinitionModels.Controls.booleanInstance).typeVariables = ∅ := by
    decide +kernel
  constructor
  · apply model_symbol_local
    intro parameter member
    simp only [Ty.fromHOL_toHOL, abstractionClosed, Finset.notMem_empty] at member
  · apply model_symbol_local
    intro parameter member
    simp only [Ty.fromHOL_toHOL, representationClosed, Finset.notMem_empty] at member

/-- The polymorphic installed abstraction retains its exact map under an
update to a parameter absent from its original public annotation. -/
theorem unused_parameter_preserves_abstraction (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (unused : Domain.{w}) :
    HEq ((model DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other (Function.update assignment (Name.global "unused") unused)).constDen
      (.constant polymorphicResult.output.abstractionConstant
        (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl))
      ((model DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
        polymorphic_existence_proven other assignment).constDen
        (.constant polymorphicResult.output.abstractionConstant
          (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl)) := by
  have unusedAbsent : Name.global "unused" ∉
      (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty).typeVariables := by
    decide +kernel
  apply model_symbol_local
  intro parameter member
  rw [Ty.fromHOL_toHOL] at member
  apply Function.update_of_ne
  intro equal
  exact unusedAbsent (equal ▸ member)

private def marked : Domain.{w} := ⟨ULift.{w + 1, 0} Prop, .up True⟩

private theorem marked_ne_proposition : marked.{w} ≠ proposition := by
  intro equal
  have same : (True : Prop) = False :=
    congrArg (fun value : ULift.{w + 1, 0} Prop => value.down) (eq_of_heq (Domain.mk.inj equal).2)
  exact Eq.mp same True.intro

/-- Domain tuples preserve the chosen inhabitants as well as carrier types.
A changed used parameter cannot be discarded as an unused assignment. -/
theorem used_parameter_changes_tuple (other : OperatorFamilies.{w}) :
    instanceArguments DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other (fun _ => marked.{w}) TypeSubst.empty ≠
    instanceArguments DefinitionHistoryModels.Controls.polymorphicDefinitions polymorphic_result_admitted
      polymorphic_existence_proven other (fun _ => proposition.{w}) TypeSubst.empty := by
  simp only [instanceArguments, original_parameter_table, List.map_cons, List.map_nil]
  simp only [reindex, TypeSubst.apply_empty, evaluate_var]
  intro equal
  exact marked_ne_proposition (List.cons.inj equal).1

end Controls

end Mettapedia.Languages.HOLLight.UniformTypeDefinitionSupport
