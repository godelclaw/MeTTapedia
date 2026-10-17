import Mettapedia.Languages.HOLLight.MixedDefinitionHistory
import Mettapedia.Languages.HOLLight.DefinitionModelFamily

/-!
# Constructed predecessor families for original mixed histories

The semantic state retains the actual source history. Initial and constant
constructors earn their invariants; a witnessed type family is built from
a preceding syntactic proof and that constructed state. The carrier-changing
installation and the arbitrary mixed-history recursion are subsequent joins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MixedDefinitionModelFamily

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionHistory ConstantHistoryExpandedTypes

universe w

/-- Original primitive licences specialize the canonical semantic family. -/
abbrev Primitives := DefinitionModelFamily.Primitives

/-- A semantic construction state over the exact original history. The
constructor theorems below earn these properties; they are not an acceptance
predicate or an additional source calculus. -/
structure Construction {initial final : TheoryContext} {records : List Theorem}
    (history : History initial final records) : Type (w + 2) where
  operators : OperatorFamilies.{w} → OperatorFamilies.{w}
  model : OperatorFamilies.{w} → Assignment.{w} → HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol
  carrier : ∀ other assignment, (model other assignment).Carrier = atomicCarrier (operators other) assignment
  fullDomains : ∀ other assignment, (model other assignment).FullDomains
  localSymbols : ∀ other, ModelAssignmentSupport.SymbolLocal (model other)
  equations : ∀ other assignment formula, formula ∈ equationTheory records → (model other assignment).models formula
  freshOperators : ∀ other operator family, operator ≠ TypeOp.bool → operator ≠ TypeOp.function →
    final.signature.typeOperators operator = none →
    operators (extend other operator family) = extend (operators other) operator family
  freshModels : ∀ other operator family, operator ≠ TypeOp.bool → operator ≠ TypeOp.function →
    final.signature.typeOperators operator = none → ∀ assignment,
    SourceAgreement final.signature (model (extend other operator family) assignment) (model other assignment)
  instances : ∀ other later,
    (∀ operator arity, final.signature.typeOperators operator = some arity → later.typeOperators operator = some arity) →
    ∀ assignment substitution,
    SourceAgreement (withTypes final.signature later)
      (model other (reindex (primitiveFamilies (operators other)) substitution assignment))
      (reindexedModel substitution (model other assignment))

namespace Construction

variable {initial final : TheoryContext} {records : List Theorem}
  {history : History initial final records}

/-- The original construction specializes the canonical predecessor family. -/
def toFamily (prior : Construction.{w} history) :
    DefinitionModelFamily.Family.{w} initial final (equationTheory records) where
  includes := history.includes
  operators := prior.operators
  model := prior.model
  carrier := prior.carrier
  fullDomains := prior.fullDomains
  localSymbols := prior.localSymbols
  equations := prior.equations
  freshOperators := prior.freshOperators
  freshModels := prior.freshModels
  instances := prior.instances

/-- The actual coherent initial interpretation starts the construction. -/
noncomputable def nil (primitives : Primitives initial) : Construction.{w} (History.nil : History initial initial []) where
  operators := id
  model := initialModel
  carrier := initialModel_carrier
  fullDomains := initialModel_fullDomains
  localSymbols := initial_symbol_local
  equations := by
    intro other assignment formula member
    rw [equationTheory_nil] at member
    exact absurd member (Set.notMem_empty _)
  freshOperators := fun _ _ _ _ _ _ => rfl
  freshModels := initial_operator_agreement initial.signature
  instances := by
    intro other later types assignment substitution
    exact history_instance_agreement
      (DefinitionHistoryModels.ConstantHistory.nil : DefinitionHistoryModels.ConstantHistory initial initial)
      later types primitives.functionArity primitives.equalityParameter primitives.equalityRegistered
      primitives.selectionParameter primitives.selectionDeclaration other assignment substitution

/-- The exact original admitted constant extension earns all semantic-state
invariants, including future type-table instances and earlier mixed equations. -/
noncomputable def constant (primitives : Primitives initial) (prior : Construction.{w} history)
    (instances : InstanceWitnesses) (name : Name) (source : SourceTerm)
    (result : ContextConstantDefinitionResult)
    (accepted : admitConstantInTheory final instances name source = some result) :
    Construction.{w} (History.constant history instances name source result accepted) where
  operators := prior.operators
  model := fun other assignment => ConstantAdmission.sourceExtension result (prior.model other assignment)
  carrier := prior.carrier
  fullDomains := fun other assignment => ConstantAdmission.sourceExtension_fullDomains _ _ (prior.fullDomains other assignment)
  localSymbols := fun other => ModelAssignmentSupport.sourceExtension_symbol_local accepted (prior.operators other)
    (prior.model other) (prior.carrier other) (prior.fullDomains other) (prior.localSymbols other)
  equations := fun other assignment => history.models_constant_extension primitives.functionArity
    primitives.equalityParameter primitives.equalityRegistered accepted _ (prior.equations other assignment)
  freshOperators := by
    intro other operator family notBool notFunction fresh
    apply prior.freshOperators other operator family notBool notFunction
    simpa only [admitted_constant_signature accepted, Signature.addConstant] using fresh
  freshModels := by
    intro other operator family notBool notFunction fresh assignment
    have priorFresh : final.signature.typeOperators operator = none := by
      simpa only [admitted_constant_signature accepted, Signature.addConstant] using fresh
    exact (prior.freshModels other operator family notBool notFunction priorFresh assignment).constantExtension accepted
      (history.includes.1 _ _ primitives.functionArity)
      (prior.fullDomains _ _) (prior.fullDomains _ _)
  instances := by
    intro other later types assignment substitution
    have priorTypes : ∀ operator arity, final.signature.typeOperators operator = some arity → later.typeOperators operator = some arity := by
      intro operator arity found
      apply types operator arity
      simpa only [admitted_constant_signature accepted, Signature.addConstant] using found
    have first := constantExtension_agreement accepted later priorTypes
      (history.includes.1 _ _ primitives.functionArity) (prior.instances other later priorTypes assignment substitution)
      (prior.fullDomains _ _) (reindexedModel_fullDomains _ _)
    exact ConstantHistoryInstanceCoherence.sourceAgreement_trans first
      (sourceExtension_reindex_agreement accepted later priorTypes primitives.equalityParameter
        (history.includes.2 _ _ primitives.equalityRegistered) (prior.model other assignment)
        (prior.fullDomains _ _) substitution)

theorem constant_instance (prior : Construction.{w} history) (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (constant : Const) (schema : Ty)
    (formed : TypeFormed final.signature schema)
    (declared : ConstantInstance final.signature constant schema) :
    HEq ((prior.model other (reindex (primitiveFamilies (prior.operators other)) substitution assignment)).constDen
        (.constant constant schema rfl))
      ((prior.model other assignment).constDen (.constant constant (substitution.apply schema) rfl)) := by
  exact DefinitionModelFamily.Family.constant_instance
    (initial := initial)
    (final := final)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)
    (constant := constant)
    (schema := schema)
    (formed := formed)
    (declared := declared)

theorem variable_instance (prior : Construction.{w} history) (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (sourceVar : SourceVar) (formed : TypeFormed final.signature sourceVar.ty) :
    HEq ((prior.model other (reindex (primitiveFamilies (prior.operators other)) substitution assignment)).constDen
        (.variable sourceVar rfl))
      ((prior.model other assignment).constDen (.variable (substitution.applyVar sourceVar) rfl)) := by
  exact DefinitionModelFamily.Family.variable_instance
    (initial := initial)
    (final := final)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)
    (sourceVar := sourceVar)
    (formed := formed)

theorem reindex_fresh_parameters (prior : Construction.{w} history) (other : OperatorFamilies.{w})
    (later : Signature) (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (freshCurrent : final.signature.typeOperators operator = none)
    (freshLater : later.typeOperators operator = none)
    (assignment : Assignment.{w}) (substitution : TypeSubst) (schema : Ty)
    (formed : TypeFormed (withTypes final.signature later) (substitution.apply schema)) :
    ∀ parameter ∈ schema.typeVariables,
      reindex (primitiveFamilies (prior.operators (extend other operator replacement))) substitution assignment parameter =
        reindex (primitiveFamilies (prior.operators other)) substitution assignment parameter := by
  exact DefinitionModelFamily.Family.reindex_fresh_parameters
    (initial := initial)
    (final := final)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (other := other)
    (later := later)
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (freshCurrent := freshCurrent)
    (freshLater := freshLater)
    (assignment := assignment)
    (substitution := substitution)
    (schema := schema)
    (formed := formed)

theorem freshModels_withTypes (prior : Construction.{w} history) (other : OperatorFamilies.{w})
    (later : Signature)
    (types : ∀ operator arity, final.signature.typeOperators operator = some arity → later.typeOperators operator = some arity)
    (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (freshLater : later.typeOperators operator = none) (assignment : Assignment.{w}) :
    SourceAgreement (withTypes final.signature later)
      (prior.model (extend other operator replacement) assignment) (prior.model other assignment) := by
  exact DefinitionModelFamily.Family.freshModels_withTypes
    (initial := initial)
    (final := final)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (other := other)
    (later := later)
    (types := types)
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (freshLater := freshLater)
    (assignment := assignment)

/-- Actual constant prefixes use their existing chronological source
interpretation and original admission proofs, with no new evaluator. -/
noncomputable def ofConstants {final : TheoryContext}
    (primitives : Primitives initial)
    (history : DefinitionHistoryModels.ConstantHistory initial final) :
    Construction.{w} (History.ofConstants history) where
  operators := id
  model := UniformTypeDefinitionFamily.priorModel history
  carrier := UniformTypeDefinitionFamily.priorModel_carrier history
  fullDomains := UniformTypeDefinitionFamily.priorModel_fullDomains history
  localSymbols := history_initial_symbol_local history
  equations := by
    intro other assignment formula member
    rw [History.equationTheory_of_constants] at member
    exact UniformTypeDefinitionFamily.models_definitionTheory history (initialModel other assignment) formula member
  freshOperators := fun _ _ _ _ _ _ => rfl
  freshModels := fun other operator family notBool notFunction fresh assignment =>
    constantHistory_operator_agreement history primitives.functionArity other operator family
      notBool notFunction fresh assignment
  instances := fun other later types assignment substitution =>
    history_instance_agreement history later
      (fun operator arity found => types operator arity (history.includes.1 operator arity found)) primitives.functionArity
      primitives.equalityParameter primitives.equalityRegistered
      primitives.selectionParameter primitives.selectionDeclaration other assignment substitution

/-- The released all-instance uniform model is joined into the same
semantic state, with each invariant proved by its actual construction. This
provides a predecessor for a following type, rather than assuming locality
or instance coherence for an arbitrary model. -/
noncomputable def firstType {final : TheoryContext}
    (primitives : Primitives initial)
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory final instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (UniformTypeDefinitionFamily.definitionTheory history)
      (TypeAdmission.admittedImage accepted).formula) :
    Construction.{w} (History.typeDefinition (History.ofConstants history) instances request result accepted
      (by rw [History.equationTheory_of_constants]; exact proof)) where
  operators := UniformTypeDefinitionModels.operators history accepted proof
  model := UniformTypeDefinitionModels.model history accepted proof
  carrier := UniformTypeDefinitionSupport.model_carrier_eq_atomic history accepted proof
  fullDomains := UniformTypeDefinitionModels.model_fullDomains history accepted proof
  localSymbols := UniformTypeDefinitionSupport.model_symbol_local history accepted proof
  equations := fun other assignment => MixedDefinitionHistory.FirstType.models_equationTheory history accepted proof other
    primitives.functionArity primitives.equalityParameter primitives.equalityRegistered
    primitives.selectionParameter primitives.selectionDeclaration assignment
  freshOperators := fun other operator family notBool notFunction fresh =>
    UniformTypeDefinitionExtensions.operators_extend history accepted proof other operator family notBool notFunction fresh
      primitives.functionArity
  freshModels := fun other operator family notBool notFunction fresh assignment =>
    UniformTypeDefinitionExtensions.model_extend_agreement history accepted proof other operator family notBool notFunction fresh
      primitives.functionArity assignment
  instances := fun other later types assignment substitution =>
    UniformTypeDefinitionInstances.model_instance_agreement_withTypes history accepted proof other later types
      primitives.functionArity primitives.equalityParameter primitives.equalityRegistered
      primitives.selectionParameter primitives.selectionDeclaration assignment substitution

end Construction

namespace Witnessed

open UniformTypeDefinitionFamily

variable {initial context : TheoryContext} {records : List Theorem}
  {history : History initial context records}
  (prior : Construction.{w} history)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (equationTheory records) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w})

include proof in
theorem existence_models (assignment : Assignment.{w}) :
    (prior.model other assignment).models (TypeAdmission.admittedImage accepted).formula := by
  exact DefinitionModelFamily.Witnessed.existence_models
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

noncomputable def predicateDomain (assignment : Assignment.{w}) : Domain.{w} :=
  DefinitionModelFamily.Witnessed.predicateDomain
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem predicateDomain_assignment_agreement (first second : Assignment.{w})
    (agree : ∀ parameter ∈ request.typeVariables, first parameter = second parameter) :
    predicateDomain prior accepted proof other first = predicateDomain prior accepted proof other second := by
  exact DefinitionModelFamily.Witnessed.predicateDomain_assignment_agreement
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (first := first)
    (second := second)
    (agree := agree)

noncomputable def family? (arguments : List Domain.{w}) : Option Domain.{w} :=
  DefinitionModelFamily.Witnessed.family?
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (arguments := arguments)

theorem family?_wrong_arity (arguments : List Domain.{w})
    (wrong : arguments.length ≠ request.typeVariables.length) :
    family? prior accepted proof other arguments = none := by
  exact DefinitionModelFamily.Witnessed.family?_wrong_arity
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (arguments := arguments)
    (wrong := wrong)

noncomputable def family (arguments : List Domain.{w}) : Domain.{w} :=
  DefinitionModelFamily.Witnessed.family
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (arguments := arguments)

theorem family_valid (arguments : List Domain.{w})
    (arity : arguments.length = request.typeVariables.length) :
    family prior accepted proof other arguments =
      predicateDomain prior accepted proof other (tupleAssignment request.typeVariables arguments) := by
  exact DefinitionModelFamily.Witnessed.family_valid
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (arguments := arguments)
    (arity := arity)

theorem family_at_assignment (assignment : Assignment.{w}) :
    family prior accepted proof other (request.typeVariables.map assignment) =
      predicateDomain prior accepted proof other assignment := by
  exact DefinitionModelFamily.Witnessed.family_at_assignment
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem predicateDomain_extend (primitives : Primitives initial)
    (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : context.signature.typeOperators operator = none)
    (assignment : Assignment.{w}) :
    predicateDomain prior accepted proof (extend other operator replacement) assignment =
      predicateDomain prior accepted proof other assignment := by
  exact DefinitionModelFamily.Witnessed.predicateDomain_extend
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (primitives := primitives)
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (assignment := assignment)

theorem family_extend (primitives : Primitives initial)
    (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : context.signature.typeOperators operator = none) :
    family prior accepted proof (extend other operator replacement) = family prior accepted proof other := by
  exact DefinitionModelFamily.Witnessed.family_extend
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (primitives := primitives)
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)

noncomputable def operators : OperatorFamilies.{w} :=
  DefinitionModelFamily.Witnessed.operators
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)

noncomputable def carrierModel (assignment : Assignment.{w}) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  DefinitionModelFamily.Witnessed.carrierModel
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem carrierModel_carrier (assignment : Assignment.{w}) :
    (carrierModel prior accepted proof other assignment).Carrier =
      atomicCarrier (operators prior accepted proof other) assignment := by
  exact DefinitionModelFamily.Witnessed.carrierModel_carrier
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem carrierModel_fullDomains (assignment : Assignment.{w}) :
    (carrierModel prior accepted proof other assignment).FullDomains := by
  exact DefinitionModelFamily.Witnessed.carrierModel_fullDomains
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem carrierModel_new (assignment : Assignment.{w}) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty).toHOL =
      (predicateDomain prior accepted proof other assignment).Carrier := by
  exact DefinitionModelFamily.Witnessed.carrierModel_new
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem carrierModel_old_agreement (assignment : Assignment.{w}) :
    SourceAgreement context.signature (carrierModel prior accepted proof other assignment)
      (prior.model other assignment) := by
  exact DefinitionModelFamily.Witnessed.carrierModel_old_agreement
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

noncomputable def abstraction (assignment : Assignment.{w}) :
    HOL.Ty.denote.{0, w + 1} (prior.model other assignment).Carrier result.core.witness.ty.toHOL →
      (predicateDomain prior accepted proof other assignment).Carrier :=
  DefinitionModelFamily.Witnessed.abstraction
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

def representation (assignment : Assignment.{w}) :
    (predicateDomain prior accepted proof other assignment).Carrier →
      HOL.Ty.denote.{0, w + 1} (prior.model other assignment).Carrier result.core.witness.ty.toHOL :=
  DefinitionModelFamily.Witnessed.representation
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem abstraction_representation (assignment : Assignment.{w})
    (value : (predicateDomain prior accepted proof other assignment).Carrier) :
    abstraction prior accepted proof other assignment
      (representation prior accepted proof other assignment value) = value := by
  exact DefinitionModelFamily.Witnessed.abstraction_representation
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (value := value)

theorem predicate_iff_representation_abstraction (assignment : Assignment.{w})
    (value : HOL.Ty.denote.{0, w + 1} (prior.model other assignment).Carrier result.core.witness.ty.toHOL) :
    TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted) (prior.model other assignment) value ↔
      representation prior accepted proof other assignment
        (abstraction prior accepted proof other assignment value) = value := by
  exact DefinitionModelFamily.Witnessed.predicate_iff_representation_abstraction
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (value := value)

end Witnessed

namespace Controls

open DefinitionAdapters.ContextControls UniformTypeDefinitionFamily.Controls
open MixedDefinitionHistory.Controls

/-- Actual original primitive licences, rather than an abstract coherence
assumption, initialize every constructed state below. -/
def primitives : Primitives coreContext where
  functionArity := core_includes.1 _ _ function_registered
  equalityParameter := equalityParameter
  equalityRegistered := ConstantHistoryInstanceCoherence.Controls.core_equality_registered
  selectionParameter := Name.global "SelectionParameter"
  selectionDeclaration := Or.inl ConstantHistoryInstanceCoherence.Controls.core_selection_unregistered

noncomputable def firstConstruction : Construction.{w} originalFirstType :=
  Construction.firstType primitives DefinitionHistoryModels.Controls.polymorphicDefinitions
    polymorphic_result_admitted polymorphic_existence_proven

/-- The dependency-bearing actual constant after the first type earns the
same invariant family; no final mixed-history semantics are supplied. -/
noncomputable def afterFirstConstruction : Construction.{w} afterTypeHistory :=
  Construction.constant primitives firstConstruction emptyInstances afterTypeName afterTypeSource
    afterTypeResult after_type_result_admitted

theorem second_arity : secondRequest.typeVariables.length = 1 := by decide +kernel

/-- A genuinely second witnessed family is constructed over an earlier
installed type and later original constant. Its predicate contains the first
carrier, and its witness proof is the original source derivation. -/
noncomputable def secondDomain (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) : Domain.{w} :=
  Witnessed.predicateDomain afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment

theorem second_family_at_assignment (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Witnessed.family afterFirstConstruction second_result_admitted
      (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived)
      other (secondRequest.typeVariables.map assignment) = secondDomain other assignment :=
  Witnessed.family_at_assignment _ _ _ _ _

theorem second_missing_parameter_refused (other : OperatorFamilies.{w}) :
    Witnessed.family? afterFirstConstruction second_result_admitted
      (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other [] = none :=
  Witnessed.family?_wrong_arity _ _ _ _ _ (by simp [second_arity])

theorem second_excess_parameter_refused (other : OperatorFamilies.{w}) :
    Witnessed.family? afterFirstConstruction second_result_admitted
      (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived)
      other [proposition, TypeFamilySemantics.Controls.natural] = none :=
  Witnessed.family?_wrong_arity _ _ _ _ _ (by simp [second_arity])

theorem second_carrier_is_witnessed (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    HOL.Ty.denote.{0, w + 1}
      (Witnessed.carrierModel afterFirstConstruction second_result_admitted
        (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType secondRequest TypeSubst.empty).toHOL =
      (secondDomain other assignment).Carrier :=
  Witnessed.carrierModel_new _ _ _ _ _

theorem second_original_predicate_law (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (value : HOL.Ty.denote.{0, w + 1} (afterFirstConstruction.model other assignment).Carrier secondResult.core.witness.ty.toHOL) :
    TypeAdmission.representedPredicate (TypeAdmission.admittedImage second_result_admitted)
      (afterFirstConstruction.model other assignment) value ↔
      Witnessed.representation afterFirstConstruction second_result_admitted
        (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment
        (Witnessed.abstraction afterFirstConstruction second_result_admitted
          (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment value) = value :=
  Witnessed.predicate_iff_representation_abstraction _ _ _ _ _ _

/-- New ambient type reconstruction still satisfies all original preceding
rows, including all type instances of the first type's actual equations. -/
theorem second_preserves_preceding_equations (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∀ formula ∈ equationTheory
      ((DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
        (fun result => result.output.definitionTheorem) ++
        [polymorphicResult.output.abstractionRepresentationTheorem,
          polymorphicResult.output.representationAbstractionTheorem]) ++
        [afterTypeResult.output.definitionTheorem]),
      (Witnessed.carrierModel afterFirstConstruction second_result_admitted
        (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment).models formula :=
  afterFirstConstruction.equations _ assignment

def laterOperator : TypeOp := .mk (Name.global "MixedLaterScalar") .undefined

theorem later_fresh : secondResult.context.signature.typeOperators laterOperator = none := by decide +kernel

theorem later_nonprimitive : laterOperator ≠ TypeOp.bool ∧ laterOperator ≠ TypeOp.function := by
  constructor
  · intro equal
    have same := (TypeOp.same_eq_true_iff _ _).mpr equal
    have different : laterOperator.same TypeOp.bool = false := by decide +kernel
    rw [different] at same; cases same
  · intro equal
    have same := (TypeOp.same_eq_true_iff _ _).mpr equal
    have different : laterOperator.same TypeOp.function = false := by decide +kernel
    rw [different] at same; cases same

/-- Old original symbols can be compared at types formed only after the
second declaration. The absence condition applies to the later type table. -/
theorem old_alias_future_type_agreement (other : OperatorFamilies.{w})
    (replacement : List Domain.{w} → Domain.{w}) (assignment : Assignment.{w}) :
    SourceAgreement (withTypes afterTypeResult.context.signature secondResult.context.signature)
      (afterFirstConstruction.model (extend other laterOperator replacement) assignment)
      (afterFirstConstruction.model other assignment) :=
  afterFirstConstruction.freshModels_withTypes other secondResult.context.signature
    (admitSourceTypeInTheory_result second_result_admitted).1.1 laterOperator replacement
    later_nonprimitive.1 later_nonprimitive.2 later_fresh assignment

end Controls

end Mettapedia.Languages.HOLLight.MixedDefinitionModelFamily
