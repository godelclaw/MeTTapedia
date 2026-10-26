import Mettapedia.Languages.HOLLight.RegisteredReplayModels
import Mettapedia.Languages.HOLLight.RegisteredPointedTypeDefinition

/-!
# Constructed meaning of actual registered pointed-type programs

The existing witness receiver, substitution operations and source type command
are interpreted through the registered semantic-frame construction. Successful
execution yields one full-domain Henkin model of the actual returned cache.
Both pointwise laws have empty source hypotheses and hold in that constructed
model. No final interpretation or output-law truth is supplied as a premise.
The initial primitive declaration context is interpreted without extra axioms;
additional source-profile commitments retain their own initial-model obligation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RegisteredPointedModels
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open DefinitionAdapters SignatureFormation TypeFamilySemantics
open ModelInterpretation DefinitionModelFamily RegisteredReplayModels ReverseTranslation

universe w
attribute [local instance] PointedPredicateTemplate.instDecidablePredSequentEmptyAxiomPolicy

theorem replay_frame {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (context : TheoryContext) (primitives : Primitives context)
    {after : ProofExecution.Registered.State} {root : Nat}
    (accepted : RegisteredPointedPredicate.replay property context = some (after,root)) :
    Nonempty (Frame.{w} context emptyAxiomPolicy after.context after.cache) := by
  obtain ⟨before,prepared,rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨last,applied,equal⟩ := Option.bind_eq_some_iff.mp rest
  have same : last = after := congrArg Prod.fst (Option.some.inj equal)
  subst last
  have initial := initialFrame context primitives
  have registered : ProofExecution.Registered.replayFrom emptyAxiomPolicy
      (ProofExecution.Registered.empty context)
      (PointedPredicateTemplate.certificate.1.map fun node =>
        .proof node (ExportReplay.instanceCertificates context.signature)) = some before := prepared
  let frame := Frame.replay primitives _ _ initial _ registered
  exact Frame.reachable primitives frame (RegisteredSubstitution.execution_path emptyAxiomPolicy applied)

theorem finish_frame {initial : TheoryContext} {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name) (primitives : Primitives initial)
    (before : ProofExecution.Registered.State) (index : Nat)
    (frame : Frame.{w} initial emptyAxiomPolicy before.context before.cache)
    {result : RegisteredPointedTypeDefinition.Result}
    (accepted : RegisteredPointedTypeDefinition.finish property typeName abstractionName representationName before index = some result) :
    Nonempty (Frame.{w} initial emptyAxiomPolicy result.state.context result.state.cache) := by
  unfold RegisteredPointedTypeDefinition.finish at accepted
  obtain ⟨defined,admitted,rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨after,applied,equal⟩ := Option.bind_eq_some_iff.mp rest
  have same : after = result.state := congrArg RegisteredPointedTypeDefinition.Result.state (Option.some.inj equal)
  subst after
  exact ⟨Frame.apply primitives before result.state frame _ applied⟩

theorem introduce_frame {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (context : TheoryContext) (primitives : Primitives context)
    {result : RegisteredPointedTypeDefinition.Result}
    (accepted : RegisteredPointedTypeDefinition.introduce property typeName abstractionName representationName context = some result) :
    Nonempty (Frame.{w} context emptyAxiomPolicy result.state.context result.state.cache) := by
  obtain ⟨⟨before,index⟩,prepared,finished⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨frame⟩ := replay_frame property context primitives prepared
  exact finish_frame property typeName abstractionName representationName primitives before index frame finished

theorem introduce_models {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (context : TheoryContext) (primitives : Primitives context)
    {result : RegisteredPointedTypeDefinition.Result}
    (accepted : RegisteredPointedTypeDefinition.introduce property typeName abstractionName representationName context = some result)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∃ model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      model.FullDomains ∧ ∀ fact ∈ result.state.cache,
        ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
          ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) := by
  obtain ⟨frame⟩ := introduce_frame property typeName abstractionName representationName context primitives accepted
  exact ⟨frame.model other assignment,frame.model_fullDomains other assignment,
    fun _ known => frame.cached_models other assignment known⟩

theorem finish_hypotheses_empty {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (before : ProofExecution.Registered.State) (index : Nat)
    {result : RegisteredPointedTypeDefinition.Result}
    (accepted : RegisteredPointedTypeDefinition.finish property typeName abstractionName representationName before index = some result) :
    result.definition.output.abstractionRepresentationTheorem.sequent.hyp = ∅ ∧
      result.definition.output.representationAbstractionTheorem.sequent.hyp = ∅ := by
  unfold RegisteredPointedTypeDefinition.finish at accepted
  obtain ⟨defined,admitted,rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨after,_,equal⟩ := Option.bind_eq_some_iff.mp rest
  have same := Option.some.inj equal
  cases same
  have metadata := admitSourceTypeInTheory_result admitted
  have empty := (UniformTypeDefinitionFamily.admitted_parameter_guards admitted).2.2
  exact ⟨metadata.2.2.2.2.1.trans empty,metadata.2.2.2.2.2.trans empty⟩

theorem introduce_laws_models {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (context : TheoryContext) (primitives : Primitives context)
    {result : RegisteredPointedTypeDefinition.Result}
    (accepted : RegisteredPointedTypeDefinition.introduce property typeName abstractionName representationName context = some result)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∃ model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      model.FullDomains ∧
      (∃ formula, Translates [] result.definition.output.abstractionRepresentationTheorem.sequent.concl.term .prop formula ∧ model.models formula) ∧
      (∃ formula, Translates [] result.definition.output.representationAbstractionTheorem.sequent.concl.term .prop formula ∧ model.models formula) := by
  obtain ⟨frame⟩ := introduce_frame property typeName abstractionName representationName context primitives accepted
  have roots := RegisteredPointedTypeDefinition.introduce_roots property typeName abstractionName representationName context accepted
  obtain ⟨⟨before,index⟩,_,finished⟩ := Option.bind_eq_some_iff.mp accepted
  have empty := finish_hypotheses_empty property typeName abstractionName representationName before index finished
  refine ⟨frame.model other assignment,frame.model_fullDomains other assignment,?_,?_⟩
  · obtain ⟨formula,translated,holds⟩ := frame.cached_models other assignment (Array.mem_of_getElem? roots.1)
    refine ⟨formula,translated,holds ?_⟩
    rintro hypothesis ⟨term,member,_⟩
    rw [empty.1] at member
    exact absurd member (Finset.notMem_empty _)
  · obtain ⟨formula,translated,holds⟩ := frame.cached_models other assignment (Array.mem_of_getElem? roots.2)
    refine ⟨formula,translated,holds ?_⟩
    rintro hypothesis ⟨term,member,_⟩
    rw [empty.2] at member
    exact absurd member (Finset.notMem_empty _)

#print axioms finish_hypotheses_empty
#print axioms introduce_laws_models

#print axioms replay_frame
#print axioms finish_frame
#print axioms introduce_frame
#print axioms introduce_models
theorem introduce_available_models {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (context : TheoryContext) (primitives : Primitives context)
    (included : ContextControls.coreContext.signature.Includes context.signature)
    (targetFormed : TypeFormed context.signature (reverseTy target))
    (propertyFormed : AnnotationsFormed context.signature
      (reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand property)).term)
    (fresh : TypeNamesFresh context.names
      (RegisteredPointedTypeDefinition.request property typeName abstractionName representationName))
    (closed : (PointedPredicate.canonicalPredicate property).term.HasNoFreeVariables)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∃ result, RegisteredPointedTypeDefinition.introduce property typeName abstractionName representationName context = some result ∧
      ∃ model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
        model.FullDomains ∧
        (∃ formula, Translates [] result.definition.output.abstractionRepresentationTheorem.sequent.concl.term .prop formula ∧ model.models formula) ∧
        (∃ formula, Translates [] result.definition.output.representationAbstractionTheorem.sequent.concl.term .prop formula ∧ model.models formula) := by
  obtain ⟨result,accepted⟩ := RegisteredPointedTypeDefinition.introduce_available property typeName abstractionName representationName
    context included targetFormed propertyFormed fresh closed
  exact ⟨result,accepted,introduce_laws_models property typeName abstractionName representationName
    context primitives accepted other assignment⟩
#print axioms introduce_available_models
end Mettapedia.Languages.HOLLight.RegisteredPointedModels
