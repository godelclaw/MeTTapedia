import Mettapedia.Languages.HOLLight.TypeDefinitionExtensions

/-!
# Installation of original admitted source declarations

The core constructors construct every actual carrier and symbol value and
earn support, freshness and all-instance coherence. Their target theory is
empty until a chronological caller proves its retained universal background.
Retheorizing preserves the constructed interpretation and carries that
separately earned truth invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.DefinitionModelFamily.Family

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters ConstantHistoryExpandedTypes

universe w

variable {initial final : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}

/-- Attach a proved theory invariant to the same constructed interpretation. -/
def retheorize (prior : Family.{w} initial final theory) (target : HOL.ClosedTheorySet Symbol)
    (holds : ∀ other assignment formula, formula ∈ target → (prior.model other assignment).models formula) :
    Family.{w} initial final target where
  includes := prior.includes
  operators := prior.operators
  model := prior.model
  carrier := prior.carrier
  fullDomains := prior.fullDomains
  localSymbols := prior.localSymbols
  equations := holds
  freshOperators := prior.freshOperators
  freshModels := prior.freshModels
  instances := prior.instances

/-- The exact original admitted constant extension earns all semantic-state
invariants, including future type-table instances and earlier mixed equations. -/
noncomputable def constantCore (primitives : Primitives initial) (prior : Family.{w} initial final theory)
    (instances : InstanceWitnesses) (name : Name) (source : SourceTerm)
    (result : ContextConstantDefinitionResult)
    (accepted : admitConstantInTheory final instances name source = some result) :
    Family.{w} initial result.context ∅ where
  includes := prior.includes.trans (admitConstantInTheory_result accepted).2.2.1
  operators := prior.operators
  model := fun other assignment => ConstantAdmission.sourceExtension result (prior.model other assignment)
  carrier := prior.carrier
  fullDomains := fun other assignment => ConstantAdmission.sourceExtension_fullDomains _ _ (prior.fullDomains other assignment)
  localSymbols := fun other => ModelAssignmentSupport.sourceExtension_symbol_local accepted (prior.operators other)
    (prior.model other) (prior.carrier other) (prior.fullDomains other) (prior.localSymbols other)
  equations := by
    intro other assignment formula impossible
    exact absurd impossible (Set.notMem_empty _)
  freshOperators := by
    intro other operator family notBool notFunction fresh
    apply prior.freshOperators other operator family notBool notFunction
    simpa only [admitted_constant_signature accepted, Signature.addConstant] using fresh
  freshModels := by
    intro other operator family notBool notFunction fresh assignment
    have priorFresh : final.signature.typeOperators operator = none := by
      simpa only [admitted_constant_signature accepted, Signature.addConstant] using fresh
    exact (prior.freshModels other operator family notBool notFunction priorFresh assignment).constantExtension accepted
      (prior.includes.1 _ _ primitives.functionArity)
      (prior.fullDomains _ _) (prior.fullDomains _ _)
  instances := by
    intro other later types assignment substitution
    have priorTypes : ∀ operator arity, final.signature.typeOperators operator = some arity → later.typeOperators operator = some arity := by
      intro operator arity found
      apply types operator arity
      simpa only [admitted_constant_signature accepted, Signature.addConstant] using found
    have first := constantExtension_agreement accepted later priorTypes
      (prior.includes.1 _ _ primitives.functionArity) (prior.instances other later priorTypes assignment substitution)
      (prior.fullDomains _ _) (reindexedModel_fullDomains _ _)
    exact ConstantHistoryInstanceCoherence.sourceAgreement_trans first
      (sourceExtension_reindex_agreement accepted later priorTypes primitives.equalityParameter
        (prior.includes.2 _ _ primitives.equalityRegistered) (prior.model other assignment)
        (prior.fullDomains _ _) substitution)


noncomputable def typeDefinitionCore {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol} (primitives : Primitives initial) (prior : Family.{w} initial context theory)
    (instances : InstanceWitnesses) (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (theory) (TypeAdmission.admittedImage accepted).formula) :
    Family.{w} initial result.context ∅ where
  includes := prior.includes.trans (admitSourceTypeInTheory_result accepted).1
  operators := Witnessed.operators prior accepted proof
  model := TypeDefinitionModels.model prior accepted proof
  carrier := TypeDefinitionModels.model_carrier_eq_atomic prior accepted proof
  fullDomains := TypeDefinitionModels.model_fullDomains prior accepted proof
  localSymbols := TypeDefinitionModels.model_symbol_local prior accepted proof
  equations := by
    intro other assignment formula impossible
    exact absurd impossible (Set.notMem_empty _)
  freshOperators := fun other operator family notBool notFunction fresh =>
    TypeDefinitionExtensions.operators_extend prior accepted proof other operator family notBool notFunction fresh primitives
  freshModels := fun other operator family notBool notFunction fresh assignment =>
    TypeDefinitionExtensions.model_extend_agreement prior accepted proof other operator family notBool notFunction fresh primitives assignment
  instances := fun other later types assignment substitution =>
    TypeDefinitionModels.model_instance_agreement_withTypes prior accepted proof other assignment later types substitution

end Mettapedia.Languages.HOLLight.DefinitionModelFamily.Family
