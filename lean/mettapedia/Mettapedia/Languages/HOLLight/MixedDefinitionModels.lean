import Mettapedia.Languages.HOLLight.MixedTypeDefinitionExtensions

/-!
# Constructed models of original mixed definition histories

Each chronological source admission constructs the next interpretation and
earns its carrier, support, type-instance and earlier-equation invariants.
Type extensions use an actual preceding-theory proof of their retained
existence application. No final interpretation or coherence premise is
supplied to the recurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MixedDefinitionModelFamily.Construction

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionHistory

universe w

/-- An actual original type admission closes every constructed-state field.
The genuine witnessed family, original symbol installation, preceding theory
and source instance laws are all earned in the component constructions. -/
noncomputable def typeDefinition {initial context : TheoryContext} {records : List Theorem}
    {history : History initial context records} (primitives : Primitives initial) (prior : Construction.{w} history)
    (instances : InstanceWitnesses) (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable (equationTheory records) (TypeAdmission.admittedImage accepted).formula) :
    Construction.{w} (History.typeDefinition history instances request result accepted proof) where
  operators := Witnessed.operators prior accepted proof
  model := MixedTypeDefinitionModels.model prior accepted proof
  carrier := MixedTypeDefinitionModels.model_carrier_eq_atomic prior accepted proof
  fullDomains := MixedTypeDefinitionModels.model_fullDomains prior accepted proof
  localSymbols := MixedTypeDefinitionModels.model_symbol_local prior accepted proof
  equations := fun other assignment => MixedTypeDefinitionModels.models_equationTheory prior accepted proof other assignment primitives
  freshOperators := fun other operator family notBool notFunction fresh =>
    MixedTypeDefinitionExtensions.operators_extend prior accepted proof other operator family notBool notFunction fresh primitives
  freshModels := fun other operator family notBool notFunction fresh assignment =>
    MixedTypeDefinitionExtensions.model_extend_agreement prior accepted proof other operator family notBool notFunction fresh primitives assignment
  instances := fun other later types assignment substitution =>
    MixedTypeDefinitionModels.model_instance_agreement_withTypes prior accepted proof other assignment later types substitution

/-- Recursion over the exact original chronological carrier constructs the
whole model state, with arbitrary interleavings of admitted constants and
types and the actual preceding existence proof at every type step. -/
noncomputable def build {initial context : TheoryContext} {records : List Theorem}
    (primitives : Primitives initial) (history : History initial context records) : Construction.{w} history := by
  induction history with
  | nil => exact nil primitives
  | constant prior instances name source result accepted ih =>
      exact constant primitives ih instances name source result accepted
  | typeDefinition prior instances request result accepted existence ih =>
      exact typeDefinition primitives ih instances request result accepted existence

end Mettapedia.Languages.HOLLight.MixedDefinitionModelFamily.Construction

namespace Mettapedia.Languages.HOLLight.MixedDefinitionModels

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionHistory MixedDefinitionModelFamily

universe w

variable {initial context : TheoryContext} {records : List Theorem}
  (primitives : Primitives initial) (history : History initial context records)
  (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

/-- One actual interpretation of the entire source chronology. -/
noncomputable def model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  (Construction.build primitives history).model other assignment

theorem fullDomains : (model primitives history other assignment).FullDomains :=
  (Construction.build primitives history).fullDomains other assignment

/-- Every stored original equation and all its source instances are true
in the recursively constructed model of the whole mixed history. -/
theorem models_equations :
    ∀ formula ∈ equationTheory records, (model primitives history other assignment).models formula :=
  (Construction.build primitives history).equations other assignment

theorem models_record {recorded : Theorem} (member : recorded ∈ records) (substitution : TypeSubst)
    {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB recorded.sequent.concl.term) .prop formula) :
    (model primitives history other assignment).models formula :=
  models_equations primitives history other assignment formula ⟨recorded, member, substitution, translation⟩

/-- Syntactic proofs from the actual preceding equation theory are sound
in the constructed final model. This is source-kernel semantics, not a claim
about an implementation or arbitrary additional external axiom policies. -/
theorem models_provable {formula : HOL.ClosedFormula Symbol}
    (proof : HOL.ClosedTheorySet.Provable (equationTheory records) formula) :
    (model primitives history other assignment).models formula :=
  provable_models proof _ (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _
    (fullDomains primitives history other assignment)) (models_equations primitives history other assignment)

/-- Every old registered symbol follows the original type substitution,
even when its annotation is formed in a subsequent registry. -/
theorem source_instances (later : Signature)
    (types : ∀ operator arity, context.signature.typeOperators operator = some arity → later.typeOperators operator = some arity)
    (substitution : TypeSubst) :
    SourceAgreement (ConstantHistoryExpandedTypes.withTypes context.signature later)
      (model primitives history other
        (reindex (primitiveFamilies ((Construction.build primitives history).operators other)) substitution assignment))
      (reindexedModel substitution (model primitives history other assignment)) :=
  (Construction.build primitives history).instances other later types assignment substitution

/-- Parameter support is constructed through every original admission. -/
theorem symbol_local : ModelAssignmentSupport.SymbolLocal (model primitives history other) :=
  (Construction.build primitives history).localSymbols other

/-- Every formed original initial-language sentence retains exactly its
truth through all actual mixed constant and carrier-changing type steps. -/
theorem models_initial {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (formed : AnnotationsFormed initial.signature term)
    (translation : TranslatesCompositionally [] term .prop formula) :
    (model primitives history other assignment).models formula ↔ (initialModel other assignment).models formula := by
  induction history with
  | nil => exact Iff.rfl
  | constant prior instances name source result accepted ih =>
      exact (ConstantAdmission.sourceExtension_preserves_old_truth accepted
        ((Construction.build primitives prior).model other assignment) (formed.mono prior.includes) translation).trans ih
  | typeDefinition prior instances request result accepted existence ih =>
      exact (MixedTypeDefinitionModels.model_models_old (Construction.build primitives prior) accepted existence
        other assignment primitives.functionArity translation (formed.mono prior.includes)).trans ih

include primitives history other assignment in
/-- The actually constructed model refuses falsity, so the original mixed
retained-equation theory cannot derive it. -/
theorem not_provable_falsity :
    ¬ HOL.ClosedTheorySet.Provable (equationTheory records) (.bot : HOL.ClosedFormula Symbol) := by
  intro contradiction
  have impossible := models_provable primitives history other assignment contradiction
  exact impossible

namespace Controls

open MixedDefinitionHistory.Controls MixedDefinitionModelFamily.Controls

/-- The actual interleaving of two type extensions and dependent constants
has a constructed full-domain model of all seven original retained rows. -/
theorem two_types_have_model (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∃ actual : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol,
      actual.FullDomains ∧ ∀ formula ∈ equationTheory
        (((DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
          (fun result => result.output.definitionTheorem) ++
          [UniformTypeDefinitionFamily.Controls.polymorphicResult.output.abstractionRepresentationTheorem,
           UniformTypeDefinitionFamily.Controls.polymorphicResult.output.representationAbstractionTheorem]) ++
          [afterTypeResult.output.definitionTheorem]) ++
          [secondResult.output.abstractionRepresentationTheorem, secondResult.output.representationAbstractionTheorem]),
        actual.models formula :=
  ⟨model MixedDefinitionModelFamily.Controls.primitives twoTypesHistory other assignment, fullDomains MixedDefinitionModelFamily.Controls.primitives twoTypesHistory other assignment,
    models_equations MixedDefinitionModelFamily.Controls.primitives twoTypesHistory other assignment⟩

def afterTwoTypesSource : SourceTerm :=
  .const secondResult.output.representationConstant
    (UniformTypeDefinitionModels.representationAnnotation (request := secondRequest) (result := secondResult) TypeSubst.empty)

def afterTwoTypesName : Name := Name.global "mixedAfterTwoTypesAlias"

theorem after_two_types_admitted :
    (admitConstantInTheory secondResult.context emptyInstances afterTwoTypesName afterTwoTypesSource).isSome = true := by
  decide +kernel

def afterTwoTypesResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory secondResult.context emptyInstances afterTwoTypesName afterTwoTypesSource).get
    (by rw [after_two_types_admitted])

theorem after_two_types_result_admitted :
    admitConstantInTheory secondResult.context emptyInstances afterTwoTypesName afterTwoTypesSource = some afterTwoTypesResult :=
  (Option.some_get after_two_types_admitted).symm

noncomputable def afterTwoTypesHistory : History DefinitionAdapters.ContextControls.coreContext afterTwoTypesResult.context
    ((((DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
      (fun result => result.output.definitionTheorem) ++
      [UniformTypeDefinitionFamily.Controls.polymorphicResult.output.abstractionRepresentationTheorem,
       UniformTypeDefinitionFamily.Controls.polymorphicResult.output.representationAbstractionTheorem]) ++
      [afterTypeResult.output.definitionTheorem]) ++
      [secondResult.output.abstractionRepresentationTheorem, secondResult.output.representationAbstractionTheorem]) ++
      [afterTwoTypesResult.output.definitionTheorem]) :=
  .constant twoTypesHistory emptyInstances afterTwoTypesName afterTwoTypesSource afterTwoTypesResult after_two_types_result_admitted

/-- A dependency-bearing original constant following both type steps is
included in the same recurrence and all eight rows remain true. -/
theorem after_two_types_models (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∀ formula ∈ equationTheory
      ((((DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
        (fun result => result.output.definitionTheorem) ++
        [UniformTypeDefinitionFamily.Controls.polymorphicResult.output.abstractionRepresentationTheorem,
         UniformTypeDefinitionFamily.Controls.polymorphicResult.output.representationAbstractionTheorem]) ++
        [afterTypeResult.output.definitionTheorem]) ++
        [secondResult.output.abstractionRepresentationTheorem, secondResult.output.representationAbstractionTheorem]) ++
        [afterTwoTypesResult.output.definitionTheorem]),
      (model MixedDefinitionModelFamily.Controls.primitives afterTwoTypesHistory other assignment).models formula :=
  models_equations MixedDefinitionModelFamily.Controls.primitives afterTwoTypesHistory other assignment

theorem premature_second_alias_refused :
    admitConstantInTheory afterTypeResult.context emptyInstances afterTwoTypesName afterTwoTypesSource = none := by
  decide +kernel

end Controls

end Mettapedia.Languages.HOLLight.MixedDefinitionModels
