import Mettapedia.Languages.HOLLight.RegisteredPointedPredicate
import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionFormation

/-!
# Registered type definitions from cached pointed witnesses

A received pointed witness supplies the source existence theorem. Actual source
admission constructs the extended signature, whose instance certificates check
both the original inputs and the two newly registered maps. Formation of the
two pointwise laws follows from their existing structural construction; neither
law's formation is a premise. Fresh names and predicate closedness remain
explicit. This construction does not identify a complete datatype compiler or
a native implementation refinement.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RegisteredPointedTypeDefinition
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open DefinitionAdapters SignatureFormation ReverseTranslation
attribute [local instance] PointedPredicateTemplate.instDecidablePredSequentEmptyAxiomPolicy

def request {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name) : TypeOperatorDefinitionRequest :=
  { (PointedPredicate.request property typeName abstractionName representationName) with
    existence := (PointedPredicateInstantiation.specializedProof property).result }

theorem definition_available {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (before : ProofExecution.Registered.State) (index : Nat)
    (known : before.cache[index]? = some (PointedPredicateInstantiation.specializedProof property).result)
    (valid : ProofExecution.Registered.Valid emptyAxiomPolicy before)
    (fresh : TypeNamesFresh before.context.names
      (request property typeName abstractionName representationName))
    (closed : (PointedPredicate.canonicalPredicate property).term.HasNoFreeVariables)
    (functionRegistered : before.context.signature.typeOperators TypeOp.function = some 2)
    (booleanFormed : TypeFormed before.context.signature Ty.bool)
    (equalityParameter : Name)
    (equalityRegistered : before.context.signature.constants Const.equality =
      some (Ty.equality (.var equalityParameter))) :
    ∃ result after,
      admitSourceTypeInTheory before.context (ExportReplay.instanceCertificates before.context.signature)
        (request property typeName abstractionName representationName) = some result ∧
      ProofExecution.Registered.apply emptyAxiomPolicy before
        (.typeDefinition ("registered-pointed-type-definition",0)
          (request property typeName abstractionName representationName)
          index (ExportReplay.instanceCertificates result.context.signature)) = some after := by
  let selected := request property typeName abstractionName representationName
  have derived := valid _ (Array.mem_of_getElem? known)
  have formed := derived.wellFormed
  have application := PointedPredicateInstantiation.specialized_application property
  obtain ⟨domain,codomain,_,_,shape⟩ := application
  have conclusion := formed.1.1
  rw [shape] at conclusion
  have predicateFormed : AnnotationsFormed before.context.signature
      (PointedPredicate.canonicalPredicate property).term := by
    cases conclusion with | app first _ => exact first
  have pointFormed : AnnotationsFormed before.context.signature
      (PointedPredicate.canonicalPoint target).term := by
    cases conclusion with | app _ second => exact second
  have carrierFormed := pointFormed.inferredType before.context.signature functionRegistered
    (by simp [ContextFormed]) (PointedPredicate.canonicalPoint target).checked
  have admissible : TypeAdmissible before.context.names selected := by
    refine ⟨fresh, ⟨PointedPredicate.canonicalPredicate property, PointedPredicate.canonicalPoint target,
      PointedPredicateInstantiation.specialized_application property,
      PointedPredicate.predicate_source_checked property,
      PointedPredicateInstantiation.specialized_hypotheses property,
      PointedPredicateInstantiation.specialized_boolean property, closed,
      sortedParameters_nodup _, ?_⟩,rfl⟩
    change (sortedParameters (PointedPredicate.predicateSource property)).toFinset =
      (PointedPredicate.canonicalPredicate property).term.typeVariables
    rw [sortedParameters_support]
    exact congrArg DBTerm.typeVariables
      (congrArg CanonicalTerm.term
        (PrimitiveTransport.checkedSource_exact (PointedPredicate.canonicalPredicate property)))
  have available : (admitSourceTypeInTheory before.context
      (ExportReplay.instanceCertificates before.context.signature) selected).isSome = true := by
    rw [admitSourceTypeInTheory_isSome_eq,
      admitTypeInTheory_eq_fromApplication _ _ _ _ _
        (PointedPredicateInstantiation.specialized_application property)]
    apply (admitTypeInTheoryFromApplication_isSome_iff _ _ _ _ _ _).mpr
    exact ⟨(TypeInstantiationCertificates.annotationsFormedB_exact _ _).mpr predicateFormed,
      (TypeInstantiationCertificates.annotationsFormedB_exact _ _).mpr pointFormed,
      carrierFormed, functionRegistered, admissible⟩
  obtain ⟨result,admitted⟩ := Option.isSome_iff_exists.mp available
  have laws := MeTTa.TypeDefinitionFormation.source_outputs_formed before.context
    (ExportReplay.instanceCertificates before.context.signature) selected
    (PointedPredicate.canonicalPredicate property) (PointedPredicate.canonicalPoint target)
    (PointedPredicateInstantiation.specialized_application property) (PointedPredicateInstantiation.specialized_boolean property) result
    admitted formed functionRegistered booleanFormed equalityParameter equalityRegistered
  let instances := ExportReplay.instanceCertificates result.context.signature
  have included := (admitSourceTypeInTheory_result admitted).1
  have completeOld := TypeInstantiationCertificates.annotationsFormedB_complete_of_includes before.context.signature
    result.context.signature included
  have newAvailable : (admitSourceTypeInTheory before.context instances selected).isSome = true := by
    rw [admitSourceTypeInTheory_isSome_eq,
      admitTypeInTheory_eq_fromApplication _ _ _ _ _
        (PointedPredicateInstantiation.specialized_application property)]
    exact (admitTypeInTheoryFromApplication_isSome_iff _ _ _ _ _ _).mpr
      ⟨completeOld _ predicateFormed,completeOld _ pointFormed,carrierFormed,functionRegistered,admissible⟩
  obtain ⟨other,newAdmitted⟩ := Option.isSome_iff_exists.mp newAvailable
  have same := admitSourceTypeInTheory_unique before.context
    (ExportReplay.instanceCertificates before.context.signature) instances selected result other admitted newAdmitted
  rw [← same] at newAdmitted
  have found : before.cache[index]? = some selected.existence := known
  have firstFormed : theoremFormedB result.context.signature instances
      result.output.abstractionRepresentationTheorem = true :=
    (TypeInstantiationCertificates.theoremFormedB_exact _ _).mpr laws.1
  have secondFormed : theoremFormedB result.context.signature instances
      result.output.representationAbstractionTheorem = true :=
    (TypeInstantiationCertificates.theoremFormedB_exact _ _).mpr laws.2
  have checked : (ProofExecution.Registered.Command.typeDefinition
      ("registered-pointed-type-definition",0) selected index
      instances).check
      emptyAxiomPolicy before.context before.cache =
      some ⟨result.context,[result.output.abstractionRepresentationTheorem,
        result.output.representationAbstractionTheorem]⟩ := by
    simp [ProofExecution.Registered.Command.check,found,newAdmitted,
      firstFormed,secondFormed]
  refine ⟨result,?_⟩
  unfold ProofExecution.Registered.apply
  rw [checked]
  exact ⟨_,admitted,rfl⟩

#print axioms definition_available
end Mettapedia.Languages.HOLLight.RegisteredPointedTypeDefinition


set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RegisteredPointedTypeDefinition
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open DefinitionAdapters SignatureFormation ReverseTranslation
attribute [local instance] PointedPredicateTemplate.instDecidablePredSequentEmptyAxiomPolicy

structure Result where
  state : ProofExecution.Registered.State
  definition : SourceTypeDefinitionResult
  abstractionRepresentation : Nat
  representationAbstraction : Nat

def finish {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (before : ProofExecution.Registered.State) (index : Nat) : Option Result := do
  let selected := request property typeName abstractionName representationName
  let defined ← admitSourceTypeInTheory before.context
    (ExportReplay.instanceCertificates before.context.signature) selected
  let after ← ProofExecution.Registered.apply emptyAxiomPolicy before
    (.typeDefinition ("registered-pointed-type-definition",0) selected index
      (ExportReplay.instanceCertificates defined.context.signature))
  pure ⟨after,defined,before.cache.size,before.cache.size+1⟩

def introduce {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext) : Option Result := do
  let (before,index) ← RegisteredPointedPredicate.replay property context
  finish property typeName abstractionName representationName before index

theorem finish_available {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (before : ProofExecution.Registered.State) (index : Nat)
    (known : before.cache[index]? = some (PointedPredicateInstantiation.specializedProof property).result)
    (valid : ProofExecution.Registered.Valid emptyAxiomPolicy before)
    (fresh : TypeNamesFresh before.context.names (request property typeName abstractionName representationName))
    (closed : (PointedPredicate.canonicalPredicate property).term.HasNoFreeVariables)
    (functionRegistered : before.context.signature.typeOperators TypeOp.function = some 2)
    (booleanFormed : TypeFormed before.context.signature Ty.bool)
    (equalityParameter : Name)
    (equalityRegistered : before.context.signature.constants Const.equality =
      some (Ty.equality (.var equalityParameter))) :
    ∃ result, finish property typeName abstractionName representationName before index = some result := by
  obtain ⟨defined,after,admitted,applied⟩ := definition_available property typeName abstractionName representationName
    before index known valid fresh closed functionRegistered booleanFormed equalityParameter equalityRegistered
  exact ⟨⟨after,defined,before.cache.size,before.cache.size+1⟩,by simp [finish,admitted,applied]⟩

theorem introduce_available {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext)
    (included : ContextControls.coreContext.signature.Includes context.signature)
    (targetFormed : TypeFormed context.signature (reverseTy target))
    (propertyFormed : AnnotationsFormed context.signature
      (reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand property)).term)
    (fresh : TypeNamesFresh context.names (request property typeName abstractionName representationName))
    (closed : (PointedPredicate.canonicalPredicate property).term.HasNoFreeVariables) :
    ∃ result, introduce property typeName abstractionName representationName context = some result := by
  obtain ⟨before,index,prepared,sameContext,known⟩ :=
    RegisteredPointedPredicate.replay_available property context included targetFormed propertyFormed
  have valid := RegisteredPointedPredicate.replay_preserves_derivations property context prepared
  have functionRegistered := included.1 _ _ (ContextControls.core_includes.1 _ _ ContextControls.function_registered)
  have booleanFormed := ContextControls.boolean_formed.mono (ContextControls.core_includes.trans included)
  have equalityCore : ContextControls.coreContext.signature.constants Const.equality =
      some (Ty.equality (.var ContextControls.equalityParameter)) := by
    unfold ContextControls.coreContext
    exact ContextControls.baseContext.addConstant_registered _ _ _ _
  have equalityRegistered := included.2 _ _ equalityCore
  obtain ⟨result,finished⟩ := finish_available property typeName abstractionName representationName before index
    known valid (by simpa only [sameContext] using fresh) closed
    (by simpa only [sameContext] using functionRegistered)
    (by simpa only [sameContext] using booleanFormed) ContextControls.equalityParameter
    (by simpa only [sameContext] using equalityRegistered)
  exact ⟨result,by simp only [introduce,prepared]; exact finished⟩

theorem finish_preserves_derivations {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (before : ProofExecution.Registered.State) (index : Nat) {result : Result}
    (valid : ProofExecution.Registered.Valid emptyAxiomPolicy before)
    (accepted : finish property typeName abstractionName representationName before index = some result) :
    ProofExecution.Registered.Valid emptyAxiomPolicy result.state := by
  unfold finish at accepted
  obtain ⟨defined,admitted,rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨after,applied,equal⟩ := Option.bind_eq_some_iff.mp rest
  have same : after = result.state := congrArg Result.state (Option.some.inj equal)
  subst after
  exact ProofExecution.Registered.apply_preserves_derivations emptyAxiomPolicy valid applied

theorem introduce_preserves_derivations {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext) {result : Result}
    (accepted : introduce property typeName abstractionName representationName context = some result) :
    ProofExecution.Registered.Valid emptyAxiomPolicy result.state := by
  obtain ⟨⟨before,index⟩,prepared,finished⟩ := Option.bind_eq_some_iff.mp accepted
  exact finish_preserves_derivations property typeName abstractionName representationName before index
    (RegisteredPointedPredicate.replay_preserves_derivations property context prepared) finished

private theorem definition_checked_result
    (context : TheoryContext) (cache : Array Theorem) (selected : TypeOperatorDefinitionRequest)
    (index : Nat) (instances original : InstanceWitnesses) (defined : SourceTypeDefinitionResult)
    (admitted : admitSourceTypeInTheory context original selected = some defined)
    (output : ProofExecution.Registered.Output)
    (accepted : (ProofExecution.Registered.Command.typeDefinition
      ("registered-pointed-type-definition",0) selected index instances).check
      emptyAxiomPolicy context cache = some output) :
    output = ⟨defined.context,[defined.output.abstractionRepresentationTheorem,
      defined.output.representationAbstractionTheorem]⟩ := by
  simp only [ProofExecution.Registered.Command.check] at accepted
  obtain ⟨existence,found,rest⟩ := Option.bind_eq_some_iff.mp accepted
  split at rest
  · obtain ⟨other,otherAdmitted,checked⟩ := Option.bind_eq_some_iff.mp rest
    have same := admitSourceTypeInTheory_unique context original instances selected defined other admitted otherAdmitted
    cases same
    split at checked
    · exact (Option.some.inj checked).symm
    · contradiction
  · contradiction

theorem finish_exact {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (before : ProofExecution.Registered.State) (index : Nat) {result : Result}
    (accepted : finish property typeName abstractionName representationName before index = some result) :
    result.state.context = result.definition.context ∧
      result.state.cache = before.cache ++
        #[result.definition.output.abstractionRepresentationTheorem,
          result.definition.output.representationAbstractionTheorem] ∧
      result.state.receipts = before.receipts.push
        ⟨.typeDefinition ("registered-pointed-type-definition",0)
          (request property typeName abstractionName representationName) index
          (ExportReplay.instanceCertificates result.definition.context.signature),
          [result.definition.output.abstractionRepresentationTheorem,
           result.definition.output.representationAbstractionTheorem]⟩ ∧
      result.abstractionRepresentation = before.cache.size ∧
      result.representationAbstraction = before.cache.size+1 := by
  unfold finish at accepted
  obtain ⟨defined,admitted,rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨after,applied,equal⟩ := Option.bind_eq_some_iff.mp rest
  have same := Option.some.inj equal
  cases same
  obtain ⟨output,checked,context,cache,receipts⟩ := ProofExecution.Registered.apply_result emptyAxiomPolicy applied
  have outputEqual := definition_checked_result before.context before.cache
    (request property typeName abstractionName representationName) index
    (ExportReplay.instanceCertificates defined.context.signature)
    (ExportReplay.instanceCertificates before.context.signature) defined admitted output checked
  cases outputEqual
  exact ⟨context,cache,receipts,rfl,rfl⟩

theorem finish_roots {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (before : ProofExecution.Registered.State) (index : Nat) {result : Result}
    (accepted : finish property typeName abstractionName representationName before index = some result) :
    result.state.cache[result.abstractionRepresentation]? =
        some result.definition.output.abstractionRepresentationTheorem ∧
      result.state.cache[result.representationAbstraction]? =
        some result.definition.output.representationAbstractionTheorem := by
  obtain ⟨_,cache,_,first,second⟩ := finish_exact property typeName abstractionName representationName before index accepted
  rw [cache,first,second]
  simp

theorem finish_counts {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name)
    (before : ProofExecution.Registered.State) (index : Nat) {result : Result}
    (accepted : finish property typeName abstractionName representationName before index = some result) :
    result.state.cache.size = before.cache.size+2 ∧
      result.state.receipts.size = before.receipts.size+1 := by
  obtain ⟨_,cache,receipts,_,_⟩ := finish_exact property typeName abstractionName representationName before index accepted
  simp [cache,receipts]

#print axioms finish_exact
#print axioms finish_roots
#print axioms finish_counts

#print axioms finish_available
#print axioms introduce_available
#print axioms finish_preserves_derivations
#print axioms introduce_preserves_derivations

theorem introduce_roots {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext) {result : Result}
    (accepted : introduce property typeName abstractionName representationName context = some result) :
    result.state.cache[result.abstractionRepresentation]? =
        some result.definition.output.abstractionRepresentationTheorem ∧
      result.state.cache[result.representationAbstraction]? =
        some result.definition.output.representationAbstractionTheorem := by
  obtain ⟨⟨before,index⟩,_,finished⟩ := Option.bind_eq_some_iff.mp accepted
  exact finish_roots property typeName abstractionName representationName before index finished

theorem introduce_derived_laws {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext) {result : Result}
    (accepted : introduce property typeName abstractionName representationName context = some result) :
    TheoryDerives emptyAxiomPolicy result.state.context result.definition.output.abstractionRepresentationTheorem ∧
      TheoryDerives emptyAxiomPolicy result.state.context result.definition.output.representationAbstractionTheorem := by
  have valid := introduce_preserves_derivations property typeName abstractionName representationName context accepted
  have roots := introduce_roots property typeName abstractionName representationName context accepted
  exact ⟨valid _ (Array.mem_of_getElem? roots.1),valid _ (Array.mem_of_getElem? roots.2)⟩

#print axioms introduce_roots
#print axioms introduce_derived_laws

namespace Controls

def emptyProperty := RegisteredPointedPredicate.Controls.emptyProperty
def functionProperty := RegisteredPointedPredicate.Controls.functionProperty

def openProperty : HOL.ClosedTerm Symbol (.arr .prop .prop) :=
  .const (.variable ⟨Name.global "openPointedProperty",Ty.function Ty.bool Ty.bool⟩
    (by rw [Ty.toHOL_function,Ty.toHOL_bool]))

def typeName : Name := Name.global "RegisteredPointedEmpty"
def abstractionName : Name := Name.global "absRegisteredPointedEmpty"
def representationName : Name := Name.global "repRegisteredPointedEmpty"

theorem names_fresh : TypeNamesFresh ContextControls.coreContext.names
    (request emptyProperty typeName abstractionName representationName) := by
  decide +kernel

theorem property_closed : (PointedPredicate.canonicalPredicate emptyProperty).term.HasNoFreeVariables := by
  exact (DBTerm.hasNoFreeVariables_eq_true_iff _).mp (by decide +kernel)

theorem empty_available : ∃ result,
    introduce emptyProperty typeName abstractionName representationName ContextControls.coreContext = some result :=
  introduce_available emptyProperty typeName abstractionName representationName ContextControls.coreContext
    ⟨fun _ _ h => h,fun _ _ h => h⟩ RegisteredPointedPredicate.Controls.boolean_formed
    RegisteredPointedPredicate.Controls.empty_property_formed names_fresh property_closed

/-- A proof-only name for the actual available execution output. -/
noncomputable def emptyResult : Result := Classical.choose empty_available

theorem emptyResult_received :
    introduce emptyProperty typeName abstractionName representationName ContextControls.coreContext = some emptyResult :=
  Classical.choose_spec empty_available

theorem empty_valid : ProofExecution.Registered.Valid emptyAxiomPolicy emptyResult.state :=
  introduce_preserves_derivations emptyProperty typeName abstractionName representationName
    ContextControls.coreContext emptyResult_received

theorem empty_roots :
    emptyResult.state.cache[emptyResult.abstractionRepresentation]? =
        some emptyResult.definition.output.abstractionRepresentationTheorem ∧
      emptyResult.state.cache[emptyResult.representationAbstraction]? =
        some emptyResult.definition.output.representationAbstractionTheorem :=
  introduce_roots emptyProperty typeName abstractionName representationName ContextControls.coreContext emptyResult_received

theorem empty_laws :
    TheoryDerives emptyAxiomPolicy emptyResult.state.context emptyResult.definition.output.abstractionRepresentationTheorem ∧
      TheoryDerives emptyAxiomPolicy emptyResult.state.context emptyResult.definition.output.representationAbstractionTheorem :=
  introduce_derived_laws emptyProperty typeName abstractionName representationName ContextControls.coreContext emptyResult_received

def emptyRun : Option Result :=
  introduce emptyProperty typeName abstractionName representationName ContextControls.coreContext

def functionRun : Option Result :=
  introduce functionProperty (Name.global "RegisteredPointedFunction")
    (Name.global "absRegisteredPointedFunction") (Name.global "repRegisteredPointedFunction")
    ContextControls.coreContext

def outputExact (result : Result) : Bool :=
  result.state.cache[result.abstractionRepresentation]?.any
      (fun fact => fact.structuralSame result.definition.output.abstractionRepresentationTheorem) &&
    result.state.cache[result.representationAbstraction]?.any
      (fun fact => fact.structuralSame result.definition.output.representationAbstractionTheorem) &&
    result.state.cache.size == 571 && result.state.receipts.size == 570 &&
    result.abstractionRepresentation == 569 && result.representationAbstraction == 570 &&
    decide (result.definition.output.abstractionRepresentationTheorem.axioms = ∅) &&
    decide (result.definition.output.representationAbstractionTheorem.axioms = ∅)

def verdicts : List (String × Bool) :=
  [("registered-type/empty-property",emptyRun.any outputExact),
   ("registered-type/function-carrier",functionRun.any outputExact),
   ("registered-type/open-witness-received",(RegisteredPointedPredicate.replay openProperty ContextControls.coreContext).isSome),
   ("registered-type/open-predicate-refused",(introduce openProperty typeName abstractionName representationName
      ContextControls.coreContext).isNone),
   ("registered-type/stale-type-refused",(introduce emptyProperty (Name.global "bool") abstractionName representationName
      ContextControls.coreContext).isNone),
   ("registered-type/colliding-maps-refused",(introduce emptyProperty typeName abstractionName abstractionName
      ContextControls.coreContext).isNone),
   ("registered-type/missing-premise-refused",(do
      let (before,_) ← RegisteredPointedPredicate.replay emptyProperty ContextControls.coreContext
      finish emptyProperty typeName abstractionName representationName before 1000000).isNone),
   ("registered-type/repeated-definition-refused",(do
      let result ← emptyRun
      introduce emptyProperty typeName abstractionName representationName result.state.context).isNone)]

#print axioms names_fresh
#print axioms property_closed
#print axioms empty_available
end Controls
end Mettapedia.Languages.HOLLight.RegisteredPointedTypeDefinition
