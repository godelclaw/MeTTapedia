import Mettapedia.Languages.HOLLight.UniformTypeDefinitionInstances
import Mettapedia.Languages.OpenTheory.PrimitiveEqualityFormation

/-!
# Source model families and witnessed carrier installation

A family records carrier, source-symbol support, fresh-operator preservation
and source type-instance laws. A syntactic proof in its interpreted predecessor
theory constructs the genuine new predicate subtype. This semantic layer is
independent of the chronological declaration carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.DefinitionModelFamily

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters ConstantHistoryExpandedTypes

universe w

/-- Primitive declaration licences belong to the original initial context. -/
structure Primitives (initial : TheoryContext) : Type where
  functionArity : initial.signature.typeOperators TypeOp.function = some 2
  equalityParameter : Name
  equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter))
  selectionParameter : Name
  selectionDeclaration : initial.signature.constants selectionConstant = none ∨
    initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter))

/-- A semantic construction state over the exact original history. The
constructor theorems below earn these properties; they are not an acceptance
predicate or an additional source calculus. -/
structure Family (initial final : TheoryContext) (theory : HOL.ClosedTheorySet Symbol) : Type (w + 2) where
  includes : initial.signature.Includes final.signature
  operators : OperatorFamilies.{w} → OperatorFamilies.{w}
  model : OperatorFamilies.{w} → Assignment.{w} → HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol
  carrier : ∀ other assignment, (model other assignment).Carrier = atomicCarrier (operators other) assignment
  fullDomains : ∀ other assignment, (model other assignment).FullDomains
  localSymbols : ∀ other, ModelAssignmentSupport.SymbolLocal (model other)
  equations : ∀ other assignment formula, formula ∈ theory → (model other assignment).models formula
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

theorem boolean_formed (context : TheoryContext) (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    TypeFormed context.signature Ty.bool :=
  ((context.constantTypes _ _ registered).function_components _).2.function_components _ |>.2

/-- Both pointwise source equations retain the actual licensed symbols,
function/Boolean carriers and all annotations of the admitted predicate. -/
theorem type_equations_formed {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (parameter : Name)
    (equalityRegistered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    AnnotationsFormed result.context.signature result.output.abstractionRepresentationTheorem.sequent.concl.term ∧
      AnnotationsFormed result.context.signature result.output.representationAbstractionTheorem.sequent.concl.term := by
  have included := (admitSourceTypeInTheory_result accepted).1
  have registered := UniformTypeDefinitionInstances.new_constants_registered accepted
  have abstractionFormed := result.context.constantTypes _ _ registered.1
  have representationFormed := result.context.constantTypes _ _ registered.2
  have representedFormed := (SourceTypeDefinitionTransport.admitted_represented_formed accepted).mono included
  have carrierFormed := (abstractionFormed.function_components _).2
  have predicateFormed := ((admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1).mono included
  have absFormed : AnnotationsFormed result.context.signature
      (.const result.output.abstractionConstant (UniformTypeDefinitionModels.abstractionAnnotation
        (request := request) (result := result) TypeSubst.empty)) :=
    .constant abstractionFormed ⟨_, TypeSubst.empty, registered.1, TypeSubst.apply_empty _⟩
  have repFormed : AnnotationsFormed result.context.signature
      (.const result.output.representationConstant (UniformTypeDefinitionModels.representationAnnotation
        (request := request) (result := result) TypeSubst.empty)) :=
    .constant representationFormed ⟨_, TypeSubst.empty, registered.2, TypeSubst.apply_empty _⟩
  simp only [UniformTypeDefinitionModels.abstractionAnnotation,
    UniformTypeDefinitionModels.representationAnnotation, SourceTypeDefinitionTransport.sourceCarrierType,
    TypeSubst.apply_empty] at absFormed repFormed carrierFormed
  have boolFormed := (boolean_formed context parameter equalityRegistered).mono included
  have equation := PrimitiveEqualityFormation.equation_annotations result.context.signature parameter
    (functionArity := included.1 _ _ functionArity) (booleanFormed := boolFormed)
    (registered := included.2 _ _ equalityRegistered)
  have shape := admitSourceTypeInTheory_pointwise accepted
  rw [shape.2.2.2.1, shape.2.2.2.2]
  rw [← shape.2.1, ← shape.2.2.1]
  exact ⟨equation _ carrierFormed _ _ (.app absFormed (.app repFormed (.free carrierFormed))) (.free carrierFormed),
    equation _ boolFormed _ _ (.app predicateFormed (.free representedFormed))
      (equation _ representedFormed _ _ (.app repFormed (.app absFormed (.free representedFormed))) (.free representedFormed))⟩

namespace Family

variable {initial final : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}

/-- The actual coherent initial interpretation starts the construction. -/
noncomputable def nil (primitives : Primitives initial) : Family.{w} initial initial ∅ where
  includes := Signature.Includes.refl _
  operators := id
  model := initialModel
  carrier := initialModel_carrier
  fullDomains := initialModel_fullDomains
  localSymbols := initial_symbol_local
  equations := by
    intro other assignment formula member
    exact absurd member (Set.notMem_empty _)
  freshOperators := fun _ _ _ _ _ _ => rfl
  freshModels := initial_operator_agreement initial.signature
  instances := by
    intro other later types assignment substitution
    exact history_instance_agreement
      (DefinitionHistoryModels.ConstantHistory.nil : DefinitionHistoryModels.ConstantHistory initial initial)
      later types primitives.functionArity primitives.equalityParameter primitives.equalityRegistered
      primitives.selectionParameter primitives.selectionDeclaration other assignment substitution

/-- Fix one already registered ambient family while preserving source-instance
coherence and the interpretation of future fresh operators. This specializes
the input family table; it does not identify arbitrary interpreted carriers. -/
noncomputable def fixAmbientOperator {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}
    (prior : Family.{w} initial context theory) (fixed : TypeOp) (arity : Nat)
    (registered : initial.signature.typeOperators fixed = some arity)
    (family : List Domain.{w} → Domain.{w}) : Family.{w} initial context theory where
  includes := prior.includes
  operators := fun other => prior.operators (extend other fixed family)
  model := fun other => prior.model (extend other fixed family)
  carrier := fun other => prior.carrier (extend other fixed family)
  fullDomains := fun other => prior.fullDomains (extend other fixed family)
  localSymbols := fun other => prior.localSymbols (extend other fixed family)
  equations := fun other => prior.equations (extend other fixed family)
  freshOperators := by
    intro other operator replacement notBool notFunction fresh
    have different : operator ≠ fixed := by
      intro same
      subst operator
      rw [prior.includes.1 _ _ registered] at fresh
      cases fresh
    rw [extend_commute other operator fixed replacement family different]
    exact prior.freshOperators (extend other fixed family) operator replacement notBool notFunction fresh
  freshModels := by
    intro other operator replacement notBool notFunction fresh assignment
    have different : operator ≠ fixed := by
      intro same
      subst operator
      rw [prior.includes.1 _ _ registered] at fresh
      cases fresh
    rw [extend_commute other operator fixed replacement family different]
    exact prior.freshModels (extend other fixed family) operator replacement notBool notFunction fresh assignment
  instances := fun other => prior.instances (extend other fixed family)

private theorem constant_value_typed (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (constant : Const) (annotation : Ty) {left right : HOL.Ty AtomicTy}
    (leftTyped : annotation.toHOL = left) (rightTyped : annotation.toHOL = right) :
    HEq (M.constDen (.constant constant annotation leftTyped))
      (M.constDen (.constant constant annotation rightTyped)) := by
  cases leftTyped
  cases rightTyped
  rfl

private theorem variable_value_typed (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (sourceVar : SourceVar) {left right : HOL.Ty AtomicTy}
    (leftTyped : sourceVar.ty.toHOL = left) (rightTyped : sourceVar.ty.toHOL = right) :
    HEq (M.constDen (.variable sourceVar leftTyped))
      (M.constDen (.variable sourceVar rightTyped)) := by
  cases leftTyped
  cases rightTyped
  rfl

private theorem variable_values_of_equal
    (M N : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (first second : SourceVar) (same : first = second)
    (values : HEq (M.constDen (.variable first rfl)) (N.constDen (.variable first rfl))) :
    HEq (M.constDen (.variable second rfl)) (N.constDen (.variable second rfl)) := by
  cases same
  exact values

/-- Actual instance coherence gives the original constant value followed
by its source type substitution; no term retranslation is introduced. -/
theorem constant_instance (prior : Family.{w} initial final theory) (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (constant : Const) (schema : Ty)
    (formed : TypeFormed final.signature schema)
    (declared : ConstantInstance final.signature constant schema) :
    HEq ((prior.model other (reindex (primitiveFamilies (prior.operators other)) substitution assignment)).constDen
        (.constant constant schema rfl))
      ((prior.model other assignment).constDen (.constant constant (substitution.apply schema) rfl)) := by
  have compared := (prior.instances other final.signature (fun _ _ found => found) assignment substitution).constants
    constant schema rfl formed declared
  change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
    (prior.model other assignment).Carrier schema.toHOL).symm
    ((prior.model other assignment).constDen (substitution.symbolInstance (.constant constant schema rfl)))) at compared
  have actual := compared.trans (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _)
  simp only [TypeSubst.symbolInstance] at actual
  exact actual.trans (constant_value_typed _ _ _ _ rfl)

/-- Free source variables use the same actual type-instance comparison. -/
theorem variable_instance (prior : Family.{w} initial final theory) (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (sourceVar : SourceVar) (formed : TypeFormed final.signature sourceVar.ty) :
    HEq ((prior.model other (reindex (primitiveFamilies (prior.operators other)) substitution assignment)).constDen
        (.variable sourceVar rfl))
      ((prior.model other assignment).constDen (.variable (substitution.applyVar sourceVar) rfl)) := by
  have compared := (prior.instances other final.signature (fun _ _ found => found) assignment substitution).variableValues
    sourceVar rfl formed
  change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
    (prior.model other assignment).Carrier sourceVar.ty.toHOL).symm
    ((prior.model other assignment).constDen (substitution.symbolInstance (.variable sourceVar rfl)))) at compared
  have actual := compared.trans (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _)
  simp only [TypeSubst.symbolInstance] at actual
  exact actual.trans (variable_value_typed _ _ _ rfl)

/-- Formation of one actual public instance earns precisely the domain
agreement needed by its original schema after a fresh ambient extension. -/
theorem reindex_fresh_parameters (prior : Family.{w} initial final theory) (other : OperatorFamilies.{w})
    (later : Signature) (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (freshCurrent : final.signature.typeOperators operator = none)
    (freshLater : later.typeOperators operator = none)
    (assignment : Assignment.{w}) (substitution : TypeSubst) (schema : Ty)
    (formed : TypeFormed (withTypes final.signature later) (substitution.apply schema)) :
    ∀ parameter ∈ schema.typeVariables,
      reindex (primitiveFamilies (prior.operators (extend other operator replacement))) substitution assignment parameter =
        reindex (primitiveFamilies (prior.operators other)) substitution assignment parameter := by
  intro parameter member
  rw [prior.freshOperators other operator replacement notBool notFunction freshCurrent]
  exact domain_extend_formed (withTypes final.signature later) (prior.operators other) operator replacement
    notBool notFunction freshLater assignment _ (formed_instance_parameter _ substitution schema formed parameter member)

/-- Licensed old meanings are retained over any subsequent type table
excluding the newly fresh operator. The current model comparison, actual
schema instantiation and finite parameter support earn this stronger law. -/
theorem freshModels_withTypes (prior : Family.{w} initial final theory) (other : OperatorFamilies.{w})
    (later : Signature)
    (types : ∀ operator arity, final.signature.typeOperators operator = some arity → later.typeOperators operator = some arity)
    (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (freshLater : later.typeOperators operator = none) (assignment : Assignment.{w}) :
    SourceAgreement (withTypes final.signature later)
      (prior.model (extend other operator replacement) assignment) (prior.model other assignment) := by
  have freshCurrent : final.signature.typeOperators operator = none := by
    cases found : final.signature.typeOperators operator with
    | none => rfl
    | some arity => have conflict := types operator arity found; rw [freshLater] at conflict; cases conflict
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    rw [prior.carrier, prior.carrier, prior.freshOperators other operator replacement notBool notFunction freshCurrent]
    have domains := domain_extend_formed (withTypes final.signature later) (prior.operators other) operator replacement
      notBool notFunction freshLater assignment (Ty.fromHOL type) formed
    simpa only [Ty.toHOL_fromHOL] using (evaluate_toHOL _ _ _).symm.trans
      ((congrArg Domain.Carrier domains).trans (evaluate_toHOL _ _ _))
  · intro constant annotation type typed formed declared
    obtain ⟨schema, substitution, registered, same⟩ := declared
    subst annotation
    cases typed
    have schemaFormed := final.constantTypes _ _ registered
    have schemaDeclared : ConstantInstance final.signature constant schema :=
      ⟨schema, TypeSubst.empty, registered, TypeSubst.apply_empty _⟩
    have first := prior.constant_instance (extend other operator replacement) assignment substitution constant schema schemaFormed schemaDeclared
    have last := prior.constant_instance other assignment substitution constant schema schemaFormed schemaDeclared
    have compared := (prior.freshModels other operator replacement notBool notFunction freshCurrent
      (reindex (primitiveFamilies (prior.operators (extend other operator replacement))) substitution assignment)).constants
      constant schema rfl schemaFormed schemaDeclared
    have supported := prior.localSymbols other
      (reindex (primitiveFamilies (prior.operators (extend other operator replacement))) substitution assignment)
      (reindex (primitiveFamilies (prior.operators other)) substitution assignment)
      (.constant constant schema rfl)
      (by
        simpa only [Ty.fromHOL_toHOL] using
          (prior.reindex_fresh_parameters other later operator replacement
            notBool notFunction freshCurrent freshLater assignment substitution schema formed))
    exact first.symm.trans (compared.trans (supported.trans last))
  · intro sourceVar type typed formed
    cases typed
    let parameter : Name := Name.global "type-reindex"
    let original : SourceVar := ⟨sourceVar.name, .var parameter⟩
    let substitution : TypeSubst := ⟨[(parameter, sourceVar.ty)]⟩
    have originalFormed : TypeFormed final.signature original.ty := by simp only [original, TypeFormed]
    have same : substitution.applyVar original = sourceVar := by
      rcases sourceVar with ⟨name, annotation⟩
      simp [substitution, original, TypeSubst.applyVar, TypeSubst.lookup]
    have first := prior.variable_instance (extend other operator replacement) assignment substitution original originalFormed
    have last := prior.variable_instance other assignment substitution original originalFormed
    have compared := (prior.freshModels other operator replacement notBool notFunction freshCurrent
      (reindex (primitiveFamilies (prior.operators (extend other operator replacement))) substitution assignment)).variableValues
      original rfl originalFormed
    have instantiatedFormed : TypeFormed (withTypes final.signature later) (substitution.apply original.ty) := by
      simpa only [show substitution.apply original.ty = sourceVar.ty from congrArg (fun datum : SourceVar => datum.ty) same] using formed
    have supported := prior.localSymbols other
      (reindex (primitiveFamilies (prior.operators (extend other operator replacement))) substitution assignment)
      (reindex (primitiveFamilies (prior.operators other)) substitution assignment) (.variable original rfl)
      (by
        simpa only [Ty.fromHOL_toHOL] using
          (prior.reindex_fresh_parameters other later operator replacement
            notBool notFunction freshCurrent freshLater assignment substitution original.ty instantiatedFormed))
    have values := first.symm.trans (compared.trans (supported.trans last))
    exact variable_values_of_equal _ _ _ _ same values

end Family

namespace Witnessed

open UniformTypeDefinitionFamily

variable {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}
  (prior : Family.{w} initial context theory)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (theory) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w})

include proof in
/-- The preceding syntactic proof is interpreted by the constructed prior
state. No truth of the new existence statement is supplied. -/
theorem existence_models (assignment : Assignment.{w}) :
    (prior.model other assignment).models (TypeAdmission.admittedImage accepted).formula :=
  provable_models proof _
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _ (prior.fullDomains other assignment))
    (prior.equations other assignment)

/-- The new domain is the genuine predicate subtype in the constructed
preceding model; the original syntactic witness proof earns nonemptiness. -/
noncomputable def predicateDomain (assignment : Assignment.{w}) : Domain.{w} :=
  inhabitedSubtype _ (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
    (prior.model other assignment))
    ⟨⟨TypeAdmission.representedWitness (TypeAdmission.admittedImage accepted)
      (prior.model other assignment),
      TypeAdmission.witness_valid _ _ (existence_models prior accepted proof other assignment)⟩⟩

private theorem down_function_heq {firstCarrier secondCarrier : Type (w + 1)}
    (carriers : firstCarrier = secondCarrier)
    {first : firstCarrier → ULift.{w + 1, 0} Prop}
    {second : secondCarrier → ULift.{w + 1, 0} Prop}
    (functions : HEq first second) :
    HEq (fun value => (first value).down) (fun value => (second value).down) := by
  cases carriers
  exact heq_of_eq (congrArg (fun function => fun value => (function value).down) (eq_of_heq functions))

/-- Dependence on exactly the original parameter tuple is earned from the
predecessor's constructed support and the original source admission guard. -/
theorem predicateDomain_assignment_agreement (first second : Assignment.{w})
    (agree : ∀ parameter ∈ request.typeVariables, first parameter = second parameter) :
    predicateDomain prior accepted proof other first = predicateDomain prior accepted proof other second := by
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
  have carriers : HOL.Ty.denote.{0, w + 1} (prior.model other first).Carrier result.core.witness.ty.toHOL =
      HOL.Ty.denote.{0, w + 1} (prior.model other second).Carrier result.core.witness.ty.toHOL := by
    rw [prior.carrier, prior.carrier]
    exact ModelAssignmentSupport.carrier_parameter_agreement (prior.operators other) first second _ typeAgreement
  have values := ModelAssignmentSupport.denote_parameter_agreement (prior.operators other) (prior.model other)
    (prior.carrier other) (prior.fullDomains other) (prior.localSymbols other) first second
    (TypeAdmission.admittedImage accepted).predicateTranslated predicateAgreement
    (by intro parameter member; simp [ModelAssignmentSupport.contextSupport, Ty.typeVariablesList] at member)
    (fun index => nomatch index) (fun index => nomatch index) (by intro type index; nomatch index)
  apply inhabitedSubtype_congr carriers
  apply down_function_heq carriers
  exact (heq_of_eq ((prior.model other first).denote_closed_valuation_eq _ _ _)).trans
    (values.trans (heq_of_eq ((prior.model other second).denote_closed_valuation_eq _ _ _)))

/-- The exact source arity is checked before a tuple acquires a carrier. -/
noncomputable def family? (arguments : List Domain.{w}) : Option Domain.{w} :=
  if arguments.length = request.typeVariables.length then
    some (predicateDomain prior accepted proof other (tupleAssignment request.typeVariables arguments))
  else none

theorem family?_wrong_arity (arguments : List Domain.{w})
    (wrong : arguments.length ≠ request.typeVariables.length) :
    family? prior accepted proof other arguments = none := by
  simp [family?, wrong]

noncomputable def family (arguments : List Domain.{w}) : Domain.{w} :=
  (family? prior accepted proof other arguments).getD proposition

theorem family_valid (arguments : List Domain.{w})
    (arity : arguments.length = request.typeVariables.length) :
    family prior accepted proof other arguments =
      predicateDomain prior accepted proof other (tupleAssignment request.typeVariables arguments) := by
  simp [family, family?, arity]

theorem family_at_assignment (assignment : Assignment.{w}) :
    family prior accepted proof other (request.typeVariables.map assignment) =
      predicateDomain prior accepted proof other assignment := by
  rw [family_valid _ _ _ _ _ (List.length_map _)]
  exact predicateDomain_assignment_agreement prior accepted proof other _ _ (tupleAssignment_mapped _ _)

/-- The same physical source predicate value and genuine subtype survive a
later fresh ambient operator extension through the constructed predecessor. -/
theorem predicateDomain_extend (primitives : Primitives initial)
    (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : context.signature.typeOperators operator = none)
    (assignment : Assignment.{w}) :
    predicateDomain prior accepted proof (extend other operator replacement) assignment =
      predicateDomain prior accepted proof other assignment := by
  have agreement := prior.freshModels other operator replacement notBool notFunction fresh assignment
  have carriers := agreement.carriers result.core.witness.ty.toHOL
    (by simpa only [Ty.fromHOL_toHOL] using SourceTypeDefinitionTransport.admitted_represented_formed accepted)
  apply inhabitedSubtype_congr carriers
  apply down_function_heq carriers
  have values := agreement.denote (prior.includes.1 _ _ primitives.functionArity)
    (prior.fullDomains _ _) (prior.fullDomains _ _)
    (TypeAdmission.admittedImage accepted).predicateTranslated
    (admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1
    (by intro type member; cases member)
    (fun index => nomatch index) (fun index => nomatch index) (by intro type index; nomatch index)
  exact (heq_of_eq ((prior.model (extend other operator replacement) assignment).denote_closed_valuation_eq _ _ _)).trans
    (values.trans (heq_of_eq ((prior.model other assignment).denote_closed_valuation_eq _ _ _)))

theorem family_extend (primitives : Primitives initial)
    (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : context.signature.typeOperators operator = none) :
    family prior accepted proof (extend other operator replacement) = family prior accepted proof other := by
  funext arguments
  unfold family family?
  split
  · rw [predicateDomain_extend prior accepted proof other primitives operator replacement notBool notFunction fresh]
  · rfl

/-- The actual next operator table installs the newly witnessed family
into the constructed preceding table, preserving original operator identity. -/
noncomputable def operators : OperatorFamilies.{w} :=
  extend (prior.operators other) (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)

/-- Reconstruct the same preceding history over the new ambient family.
This is the actual carrier-changing phase; the new symbols are not yet
installed by this definition. -/
noncomputable def carrierModel (assignment : Assignment.{w}) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  prior.model (extend other (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)) assignment

theorem carrierModel_carrier (assignment : Assignment.{w}) :
    (carrierModel prior accepted proof other assignment).Carrier =
      atomicCarrier (operators prior accepted proof other) assignment := by
  rw [carrierModel, prior.carrier,
    prior.freshOperators other (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)
      (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
      (SourceTypeDefinitionTransport.admitted_operator_fresh accepted)]
  rfl

theorem carrierModel_fullDomains (assignment : Assignment.{w}) :
    (carrierModel prior accepted proof other assignment).FullDomains := prior.fullDomains _ _

/-- The original source carrier receives exactly the complete new witnessed
subtype at every assignment, even after previous carrier-changing steps. -/
theorem carrierModel_new (assignment : Assignment.{w}) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty).toHOL =
      (predicateDomain prior accepted proof other assignment).Carrier := by
  rw [carrierModel_carrier, ← evaluate_toHOL]
  apply congrArg Domain.Carrier
  have sourceShape : SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty =
      .op (SourceTypeDefinitionTransport.operator request) (request.typeVariables.map Ty.var) := by
    simp [SourceTypeDefinitionTransport.sourceCarrierType]
  rw [sourceShape, operators, evaluate_op,
    primitiveFamilies_extend (prior.operators other) _ _ (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2,
    extend_new]
  have arguments : (request.typeVariables.map Ty.var).map
      (evaluate (extend (primitiveFamilies (prior.operators other)) (SourceTypeDefinitionTransport.operator request)
        (family prior accepted proof other)) assignment) = request.typeVariables.map assignment := by
    simp only [List.map_map, Function.comp_def, evaluate_var]
  rw [arguments]
  exact family_at_assignment prior accepted proof other assignment

/-- Rebuilding the constructed predecessor retains every old licensed
carrier, symbol, variable and source-term denotation. -/
theorem carrierModel_old_agreement (assignment : Assignment.{w}) :
    SourceAgreement context.signature (carrierModel prior accepted proof other assignment)
      (prior.model other assignment) :=
  prior.freshModels other (SourceTypeDefinitionTransport.operator request) (family prior accepted proof other)
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted) assignment

/-- The original abstraction uses a valid inhabitant from the genuine new
subtype for values outside its predicate. -/
noncomputable def abstraction (assignment : Assignment.{w}) :
    HOL.Ty.denote.{0, w + 1} (prior.model other assignment).Carrier result.core.witness.ty.toHOL →
      (predicateDomain prior accepted proof other assignment).Carrier :=
  HOL.WitnessedTypeDefinition.abstraction
    (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted) (prior.model other assignment))
    (predicateDomain prior accepted proof other assignment).inhabitant.val
    (predicateDomain prior accepted proof other assignment).inhabitant.property

def representation (assignment : Assignment.{w}) :
    (predicateDomain prior accepted proof other assignment).Carrier →
      HOL.Ty.denote.{0, w + 1} (prior.model other assignment).Carrier result.core.witness.ty.toHOL :=
  HOL.WitnessedTypeDefinition.representation

theorem abstraction_representation (assignment : Assignment.{w})
    (value : (predicateDomain prior accepted proof other assignment).Carrier) :
    abstraction prior accepted proof other assignment
      (representation prior accepted proof other assignment value) = value :=
  HOL.WitnessedTypeDefinition.abstraction_representation _ _ _ value

theorem predicate_iff_representation_abstraction (assignment : Assignment.{w})
    (value : HOL.Ty.denote.{0, w + 1} (prior.model other assignment).Carrier result.core.witness.ty.toHOL) :
    TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted) (prior.model other assignment) value ↔
      representation prior accepted proof other assignment
        (abstraction prior accepted proof other assignment value) = value :=
  HOL.WitnessedTypeDefinition.predicate_iff_representation_abstraction _ _ _ value

end Witnessed

namespace Family

/-- Restrict constant-declaration scope while retaining the interpreted
operator table, values and theory. The type-operator table must agree. -/
noncomputable def restrictConstants {initial smaller larger : TheoryContext}
    {theory : HOL.ClosedTheorySet Symbol} (prior : Family.{w} initial larger theory)
    (initialIncluded : initial.signature.Includes smaller.signature)
    (included : smaller.signature.Includes larger.signature)
    (types : smaller.signature.typeOperators = larger.signature.typeOperators) :
    Family.{w} initial smaller theory where
  includes := initialIncluded
  operators := prior.operators
  model := prior.model
  carrier := prior.carrier
  fullDomains := prior.fullDomains
  localSymbols := prior.localSymbols
  equations := prior.equations
  freshOperators := by
    intro other operator family notBool notFunction fresh
    apply prior.freshOperators other operator family notBool notFunction
    rw [← types]
    exact fresh
  freshModels := by
    intro other operator family notBool notFunction fresh assignment
    have largerFresh : larger.signature.typeOperators operator = none := by rw [← types]; exact fresh
    exact (prior.freshModels other operator family notBool notFunction largerFresh assignment).restrictSignature included
  instances := by
    intro other later laterTypes assignment substitution
    have largerTypes : ∀ operator arity, larger.signature.typeOperators operator = some arity →
        later.typeOperators operator = some arity := by
      intro operator arity registered
      apply laterTypes operator arity
      rw [types]
      exact registered
    apply SourceAgreement.restrictSignature (larger := withTypes larger.signature later)
      (agreement := prior.instances other later largerTypes assignment substitution)
    exact ⟨fun _ _ found => found,included.2⟩

end Family

end Mettapedia.Languages.HOLLight.DefinitionModelFamily
