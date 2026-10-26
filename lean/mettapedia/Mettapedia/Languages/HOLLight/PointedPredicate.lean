import Mettapedia.Logic.HOL.PointedPredicate
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.ExportReplay
import Mettapedia.Languages.HOLLight.RegisteredProofGraph

/-!
# Native admission of guarded pointed predicates

A retained proof constructs a predicate/witness application without assuming
inhabitance of the original predicate. Source declaration formation checks
its native closedness, type parameters and registered annotations separately.

The producer also emits actual registered proof commands before the type
command. Successful introduction preserves source derivations and gives a
retained execution path. Availability requires formation of each generated
primitive request/output and of the two definition equations; these conditions
are not inferred from intrinsic term typing with arbitrary source symbols.
The controls retain an empty-predicate admission and a free-predicate refusal.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.PointedPredicate
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation DefinitionAdapters SignatureFormation
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

variable {alpha : HOL.Ty AtomicTy}

def compileWitness (property : HOL.ClosedTerm Symbol (.arr alpha .prop)) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy
    (HOL.PointedPredicate.witness (Δ := []) property)
    (HOL.PointedPredicate.witness_functionExtensionalityFree property)
    Naming.empty ("pointed-predicate-witness", 0)

def canonicalPredicate (property : HOL.ClosedTerm Symbol (.arr alpha .prop)) : CanonicalTerm :=
  reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand (HOL.PointedPredicate.predicate property))

def canonicalPoint (alpha : HOL.Ty AtomicTy) : CanonicalTerm :=
  reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand (HOL.PointedPredicate.none (Const := Symbol) alpha))

def predicateSource (property : HOL.ClosedTerm Symbol (.arr alpha .prop)) : SourceTerm :=
  (PrimitiveTransport.checkedSource (canonicalPredicate property)).source

def request (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (typeName abstractionName representationName : Name) : TypeOperatorDefinitionRequest :=
  { typeName := typeName
    abstractionName := abstractionName
    representationName := representationName
    typeVariables := sortedParameters (predicateSource property)
    predicateSource := predicateSource property
    existence := (compileWitness property).proof.result }

theorem witness_application (property : HOL.ClosedTerm Symbol (.arr alpha .prop)) :
    CanonicalTerm.ApplicationSemantics (canonicalPredicate property) (canonicalPoint alpha)
      (compileWitness property).proof.result.sequent.concl := by
  refine ⟨reverseTy (HOL.PointedPredicate.Carrier alpha), Ty.bool, ?_, rfl, ?_⟩
  · exact Ty.destFunction?_function _ _
  rw [(compileWitness property).conclusion_exact]
  rfl

theorem predicate_source_checked (property : HOL.ClosedTerm Symbol (.arr alpha .prop)) :
    (predicateSource property).check = some (canonicalPredicate property) := by
  apply (SourceTerm.check_eq_some_iff _ _).mpr
  exact congrArg CanonicalTerm.term (PrimitiveTransport.checkedSource_exact (canonicalPredicate property))

theorem request_admissible (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext)
    (fresh : TypeNamesFresh context.names (request property typeName abstractionName representationName))
    (closed : (canonicalPredicate property).term.HasNoFreeVariables) :
    TypeAdmissible context.names (request property typeName abstractionName representationName) := by
  refine ⟨fresh, ⟨canonicalPredicate property, canonicalPoint alpha,
    witness_application property, predicate_source_checked property, ?_,
    (compileWitness property).boolean, closed, sortedParameters_nodup _, ?_⟩, rfl⟩
  · exact (compileWitness property).hypotheses_exact
  · change (sortedParameters (predicateSource property)).toFinset = (canonicalPredicate property).term.typeVariables
    rw [sortedParameters_support]
    exact congrArg DBTerm.typeVariables
      (congrArg CanonicalTerm.term (PrimitiveTransport.checkedSource_exact (canonicalPredicate property)))

def admit (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext)
    (instances : InstanceWitnesses) : Option SourceTypeDefinitionResult :=
  admitSourceTypeInTheory context instances (request property typeName abstractionName representationName)

theorem admit_available (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext)
    (instances : InstanceWitnesses)
    (fresh : TypeNamesFresh context.names (request property typeName abstractionName representationName))
    (closed : (canonicalPredicate property).term.HasNoFreeVariables)
    (predicateFormed : annotationsFormedB context.signature instances (canonicalPredicate property).term = true)
    (pointFormed : annotationsFormedB context.signature instances (canonicalPoint alpha).term = true)
    (carrierFormed : TypeFormed context.signature (canonicalPoint alpha).ty)
    (functionRegistered : context.signature.typeOperators TypeOp.function = some 2) :
    (admit property typeName abstractionName representationName context instances).isSome = true := by
  unfold admit
  rw [admitSourceTypeInTheory_isSome_eq,
    admitTypeInTheory_eq_fromApplication _ _ _ _ _ (witness_application property)]
  exact (admitTypeInTheoryFromApplication_isSome_iff _ _ _ _ _ _).mpr
    ⟨predicateFormed, pointFormed, carrierFormed, functionRegistered,
      request_admissible property typeName abstractionName representationName context fresh closed⟩

#print axioms witness_application
#print axioms request_admissible
#print axioms admit_available







def witnessCommands (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (context : TheoryContext) : List ProofExecution.Registered.Command :=
  (compileWitness property).proof.certificate.1.map
    (fun node => .proof node (ExportReplay.instanceCertificates context.signature))

def replayWitness (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (context : TheoryContext) : Option ProofExecution.Registered.State :=
  ProofExecution.Registered.replayFrom emptyAxiomPolicy
    (ProofExecution.Registered.empty context) (witnessCommands property context)

/-- Formation is checked on the actual generated primitive requests and
outputs. The original predicate's inhabitance is not a premise. -/
private theorem replayCompiledAvailable (proof : CheckedProof emptyAxiomPolicy)
    (context : TheoryContext)
    (formed : ∀ node ∈ proof.certificate.1,
      ProofExecution.Registered.requestFormedB context.signature
        (ExportReplay.instanceCertificates context.signature) node.witness = true ∧
      theoremFormedB context.signature (ExportReplay.instanceCertificates context.signature)
        node.conclusion = true) :
    ∃ after, ProofExecution.Registered.replayFrom emptyAxiomPolicy
        (ProofExecution.Registered.empty context)
        (proof.certificate.1.map (fun node => .proof node (ExportReplay.instanceCertificates context.signature)))
        = some after ∧ after.context = context ∧ after.cache[proof.certificate.2]? = some proof.result := by
  obtain ⟨cache, replayed, root⟩ :=
    (ProofSystem.checker_check_iff emptyAxiomPolicy proof.result proof.certificate).mp proof.accepted
  obtain ⟨after, actual, sameContext, sameCache⟩ :=
    ProofExecution.Registered.replayProofs_available emptyAxiomPolicy (ProofExecution.Registered.empty context)
      proof.certificate.1 (ExportReplay.instanceCertificates context.signature) cache formed replayed
  exact ⟨after, actual, sameContext, sameCache ▸ root⟩

theorem replayWitness_available (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (context : TheoryContext)
    (formed : ∀ node ∈ (compileWitness property).proof.certificate.1,
      ProofExecution.Registered.requestFormedB context.signature
        (ExportReplay.instanceCertificates context.signature) node.witness = true ∧
      theoremFormedB context.signature (ExportReplay.instanceCertificates context.signature)
        node.conclusion = true) :
    ∃ after, replayWitness property context = some after ∧ after.context = context ∧
      after.cache[(compileWitness property).proof.certificate.2]? =
        some (compileWitness property).proof.result :=
  replayCompiledAvailable (compileWitness property).proof context formed

theorem replayWitness_valid (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (context : TheoryContext) {after : ProofExecution.Registered.State}
    (accepted : replayWitness property context = some after) :
    ProofExecution.Registered.Valid emptyAxiomPolicy after :=
  ProofExecution.Registered.replayFrom_preserves_derivations emptyAxiomPolicy _ _ _
    (ProofExecution.Registered.empty_valid _ _) accepted

def introduce (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext) :
    Option ProofExecution.Registered.State := do
  let before ← replayWitness property context
  ProofExecution.Registered.apply emptyAxiomPolicy before
    (.typeDefinition ("pointed-predicate-type-definition", 0)
      (request property typeName abstractionName representationName)
      (compileWitness property).proof.certificate.2
      (ExportReplay.instanceCertificates before.context.signature))

private theorem appendRegisteredStep : ∀ {first middle last : ProofExecution.Registered.State},
    (ProofExecution.Registered.gslt emptyAxiomPolicy).MultiStep first middle →
    (ProofExecution.Registered.gslt emptyAxiomPolicy).Step middle last →
    (ProofExecution.Registered.gslt emptyAxiomPolicy).MultiStep first last
  | _, _, _, .refl _, next => .step next (.refl _)
  | _, _, _, .step initial rest, next => .step initial (appendRegisteredStep rest next)

/-- Successful introduction has an actual registered source derivation for
every cached theorem, reached from the empty cache by the retained commands. -/
theorem introduce_sound (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext)
    {after : ProofExecution.Registered.State}
    (accepted : introduce property typeName abstractionName representationName context = some after) :
    ProofExecution.Registered.Valid emptyAxiomPolicy after ∧
      (ProofExecution.Registered.gslt emptyAxiomPolicy).MultiStep
        (ProofExecution.Registered.empty context) after := by
  unfold introduce at accepted
  cases prepared : replayWitness property context with
  | none => simp [prepared] at accepted
  | some before =>
    have step : ProofExecution.Registered.apply emptyAxiomPolicy before
        (.typeDefinition ("pointed-predicate-type-definition", 0)
          (request property typeName abstractionName representationName)
          (compileWitness property).proof.certificate.2
          (ExportReplay.instanceCertificates before.context.signature)) = some after := by
      simpa [prepared] using accepted
    refine ⟨ProofExecution.Registered.apply_preserves_derivations emptyAxiomPolicy
      (replayWitness_valid property context prepared) step, ?_⟩
    have path : (ProofExecution.Registered.gslt emptyAxiomPolicy).MultiStep
        (ProofExecution.Registered.empty context) before := ProofExecution.Registered.replayFrom_reachable emptyAxiomPolicy
      (ProofExecution.Registered.empty context) (witnessCommands property context) before prepared
    exact appendRegisteredStep path ⟨_, step⟩

#print axioms replayWitness_available
#print axioms replayWitness_valid
#print axioms introduce_sound





private theorem finishDefinition {before : ProofExecution.Registered.State}
    (selected : TypeOperatorDefinitionRequest) (index : Nat) (instances : InstanceWitnesses)
    (found : before.cache[index]? = some selected.existence)
    (result : SourceTypeDefinitionResult)
    (admitted : admitSourceTypeInTheory before.context instances selected = some result)
    (formed : theoremFormedB result.context.signature instances
        result.output.abstractionRepresentationTheorem = true ∧
      theoremFormedB result.context.signature instances
        result.output.representationAbstractionTheorem = true) :
    ∃ after, ProofExecution.Registered.apply emptyAxiomPolicy before
      (.typeDefinition ("pointed-predicate-type-definition", 0) selected index instances) = some after := by
  have command : (ProofExecution.Registered.Command.typeDefinition
      ("pointed-predicate-type-definition", 0) selected index instances).check
      emptyAxiomPolicy before.context before.cache =
      some ⟨result.context, [result.output.abstractionRepresentationTheorem,
        result.output.representationAbstractionTheorem]⟩ := by
    simp [ProofExecution.Registered.Command.check, found, admitted, formed.1, formed.2]
  unfold ProofExecution.Registered.apply
  rw [command]
  exact ⟨_, rfl⟩

theorem introduce_available (property : HOL.ClosedTerm Symbol (.arr alpha .prop))
    (typeName abstractionName representationName : Name) (context : TheoryContext)
    (graphFormed : ∀ node ∈ (compileWitness property).proof.certificate.1,
      ProofExecution.Registered.requestFormedB context.signature
        (ExportReplay.instanceCertificates context.signature) node.witness = true ∧
      theoremFormedB context.signature (ExportReplay.instanceCertificates context.signature)
        node.conclusion = true)
    (fresh : TypeNamesFresh context.names (request property typeName abstractionName representationName))
    (closed : (canonicalPredicate property).term.HasNoFreeVariables)
    (predicateFormed : annotationsFormedB context.signature
      (ExportReplay.instanceCertificates context.signature) (canonicalPredicate property).term = true)
    (pointFormed : annotationsFormedB context.signature
      (ExportReplay.instanceCertificates context.signature) (canonicalPoint alpha).term = true)
    (carrierFormed : TypeFormed context.signature (canonicalPoint alpha).ty)
    (functionRegistered : context.signature.typeOperators TypeOp.function = some 2)
    (lawsFormed : ∀ result,
      admitSourceTypeInTheory context (ExportReplay.instanceCertificates context.signature)
          (request property typeName abstractionName representationName) = some result →
        theoremFormedB result.context.signature (ExportReplay.instanceCertificates context.signature)
          result.output.abstractionRepresentationTheorem = true ∧
        theoremFormedB result.context.signature (ExportReplay.instanceCertificates context.signature)
          result.output.representationAbstractionTheorem = true) :
    ∃ after, introduce property typeName abstractionName representationName context = some after := by
  have available := admit_available property typeName abstractionName representationName context
    (ExportReplay.instanceCertificates context.signature) fresh closed predicateFormed pointFormed
    carrierFormed functionRegistered
  let result := (admit property typeName abstractionName representationName context
    (ExportReplay.instanceCertificates context.signature)).get available
  have admitted : admitSourceTypeInTheory context (ExportReplay.instanceCertificates context.signature)
      (request property typeName abstractionName representationName) = some result :=
    (Option.some_get available).symm
  obtain ⟨before, prepared, sameContext, root⟩ := replayWitness_available property context graphFormed
  have actualAdmission : admitSourceTypeInTheory before.context
      (ExportReplay.instanceCertificates before.context.signature)
      (request property typeName abstractionName representationName) = some result := by
    rw [sameContext]
    exact admitted
  obtain ⟨after, finished⟩ := finishDefinition (request property typeName abstractionName representationName)
    (compileWitness property).proof.certificate.2 (ExportReplay.instanceCertificates before.context.signature)
    root result actualAdmission (by rw [sameContext]; exact lawsFormed result admitted)
  refine ⟨after, ?_⟩
  unfold introduce
  rw [prepared]
  exact finished

def graphFormedB (property : HOL.ClosedTerm Symbol (.arr alpha .prop)) (context : TheoryContext) : Bool :=
  (compileWitness property).proof.certificate.1.all (fun node =>
    ProofExecution.Registered.requestFormedB context.signature
        (ExportReplay.instanceCertificates context.signature) node.witness &&
      theoremFormedB context.signature (ExportReplay.instanceCertificates context.signature) node.conclusion)

theorem graphFormedB_spec (property : HOL.ClosedTerm Symbol (.arr alpha .prop)) (context : TheoryContext) :
    graphFormedB property context = true ↔
      ∀ node ∈ (compileWitness property).proof.certificate.1,
        ProofExecution.Registered.requestFormedB context.signature
          (ExportReplay.instanceCertificates context.signature) node.witness = true ∧
        theoremFormedB context.signature (ExportReplay.instanceCertificates context.signature)
          node.conclusion = true := by
  simp [graphFormedB, List.all_eq_true]

#print axioms introduce_available
#print axioms graphFormedB_spec


namespace Controls

def falseProperty : HOL.ClosedTerm Symbol (.arr .prop .prop) := .lam .bot

def emptyWitness := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PointedPredicate.witness (Δ := []) falseProperty)
  (HOL.PointedPredicate.witness_functionExtensionalityFree falseProperty)
  Naming.empty ("pointed-empty-witness", 0)

theorem emptyWitness_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    emptyWitness.proof.result emptyWitness.proof.certificate = true := emptyWitness.proof.accepted

def emptyPredicateSource : SourceTerm :=
  (PrimitiveTransport.checkedSource (reverseCanonical Naming.empty
    (HOL.ImpredicativeConnectives.expand (HOL.PointedPredicate.predicate falseProperty)))).source

def emptyRequest : TypeOperatorDefinitionRequest :=
  { typeName := Name.global "pointedEmpty"
    abstractionName := Name.global "absPointedEmpty"
    representationName := Name.global "repPointedEmpty"
    typeVariables := []
    predicateSource := emptyPredicateSource
    existence := emptyWitness.proof.result }

def certificates : InstanceWitnesses := ExportReplay.instanceCertificates ContextControls.coreContext.signature

theorem empty_admitted :
    (admitSourceTypeInTheory ContextControls.coreContext certificates emptyRequest).isSome = true := by
  decide +kernel


def emptyResult : SourceTypeDefinitionResult :=
  (admitSourceTypeInTheory ContextControls.coreContext certificates emptyRequest).get empty_admitted

def freeProperty : HOL.Term Symbol [.arr .prop .prop] (.arr .prop .prop) := .var .vz

def freeWitness := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PointedPredicate.witness (Δ := []) freeProperty)
  (HOL.PointedPredicate.witness_functionExtensionalityFree freeProperty)
  (Naming.cons (Name.global "outsideProperty") Naming.empty) ("pointed-free-witness", 0)

theorem freeWitness_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    freeWitness.proof.result freeWitness.proof.certificate = true := freeWitness.proof.accepted

def freeRequest : TypeOperatorDefinitionRequest :=
  { typeName := Name.global "pointedFree"
    abstractionName := Name.global "absPointedFree"
    representationName := Name.global "repPointedFree"
    typeVariables := []
    predicateSource := (PrimitiveTransport.checkedSource (reverseCanonical
      (Naming.cons (Name.global "outsideProperty") Naming.empty)
      (HOL.ImpredicativeConnectives.expand (HOL.PointedPredicate.predicate freeProperty)))).source
    existence := freeWitness.proof.result }

theorem free_predicate_refused :
    (admitSourceTypeInTheory ContextControls.coreContext certificates freeRequest).isNone = true := by
  decide +kernel

#print axioms freeWitness_accepted
#print axioms free_predicate_refused

#print axioms emptyWitness_accepted
#print axioms empty_admitted



def genericRequest : TypeOperatorDefinitionRequest :=
  request falseProperty (Name.global "pointedEmpty") (Name.global "absPointedEmpty")
    (Name.global "repPointedEmpty")

theorem generic_request_admissible : TypeAdmissible ContextControls.coreContext.names genericRequest :=
  request_admissible falseProperty _ _ _ _ (by decide +kernel)
    ((DBTerm.hasNoFreeVariables_eq_true_iff _).mp (by decide +kernel))

theorem generic_empty_admitted :
    (admit falseProperty (Name.global "pointedEmpty") (Name.global "absPointedEmpty")
      (Name.global "repPointedEmpty") ContextControls.coreContext certificates).isSome = true := by
  apply admit_available
  · decide +kernel
  · exact (DBTerm.hasNoFreeVariables_eq_true_iff _).mp (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · exact (typeFormedB_eq_true_iff _ _).mp (by decide +kernel)
  · decide +kernel

def emptyIntroduced : Option ProofExecution.Registered.State :=
  introduce falseProperty (Name.global "pointedEmpty") (Name.global "absPointedEmpty")
    (Name.global "repPointedEmpty") ContextControls.coreContext

/-- The actual command interpreter appends exactly the two stored definition
laws after the complete generated witness graph. -/
def exactEmptyHistory : Bool :=
  match emptyIntroduced with
  | none => false
  | some after =>
      let proof := (compileWitness falseProperty).proof
      decide (after.cache.size = proof.certificate.1.length + 2) &&
        decide (after.receipts.size = proof.certificate.1.length + 1) &&
        (match after.cache[proof.certificate.1.length]?,
            after.cache[proof.certificate.1.length + 1]? with
          | some first, some second =>
              first.structuralSame emptyResult.output.abstractionRepresentationTheorem &&
                second.structuralSame emptyResult.output.representationAbstractionTheorem
          | _, _ => false)

def missingWitnessRefused : Bool :=
  (ProofExecution.Registered.apply emptyAxiomPolicy
    (ProofExecution.Registered.empty ContextControls.coreContext)
    (.typeDefinition ("missing-pointed-witness", 0) genericRequest
      (compileWitness falseProperty).proof.certificate.2 certificates)).isNone

/-- Intrinsic closure does not erase a free native source symbol. -/
def freeSourceProperty : HOL.ClosedTerm Symbol (.arr .prop .prop) :=
  .const (.variable ⟨Name.global "outsideProperty", Ty.function Ty.bool Ty.bool⟩
    (by simp only [Ty.toHOL_function, Ty.toHOL_bool]))

def freeSourceRefused : Bool :=
  (introduce freeSourceProperty (Name.global "pointedFreeSource")
    (Name.global "absPointedFreeSource") (Name.global "repPointedFreeSource")
    ContextControls.coreContext).isNone

def duplicateNamesRefused : Bool :=
  match emptyIntroduced with
  | none => false
  | some after =>
      (introduce falseProperty (Name.global "pointedEmpty") (Name.global "absPointedEmpty")
        (Name.global "repPointedEmpty") after.context).isNone

def verdicts : List (String × Bool) :=
  [("pointed predicate witness checks without admitted axioms",
      (ProofSystem.checker emptyAxiomPolicy).check emptyWitness.proof.result emptyWitness.proof.certificate),
   ("pointed empty predicate has native type admission",
      (admitSourceTypeInTheory ContextControls.coreContext certificates emptyRequest).isSome),
   ("pointed predicate generated graph has registered request/output formation",
      graphFormedB falseProperty ContextControls.coreContext),
   ("pointed predicate registered introduction retains the exact two definition laws", exactEmptyHistory),
   ("pointed type command refuses a missing witness history", missingWitnessRefused),
   ("pointed predicate refuses a free source predicate", freeSourceRefused),
   ("pointed type command refuses duplicate names", duplicateNamesRefused)]

#print axioms generic_request_admissible
#print axioms generic_empty_admitted

end Controls

end Mettapedia.Languages.HOLLight.PointedPredicate
