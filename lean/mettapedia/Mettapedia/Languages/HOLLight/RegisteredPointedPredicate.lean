import Mettapedia.Languages.HOLLight.PointedPredicateTemplate
import Mettapedia.Languages.HOLLight.RegisteredProofGraph
import Mettapedia.Languages.HOLLight.RegisteredSubstitution
import Mettapedia.Languages.HOLLight.PointedPredicateInstantiation

/-!
# Registered specialization of a cached pointed witness

A checked generic certificate is received in any theory signature extending
the primitive core. The existing registered substitution receiver then installs
a formed carrier and a formed predicate. Availability requires those ordinary
input-formation conditions, with no per-node witness-formation premise and no
inhabitance premise for the original predicate. The returned address contains
the exact original compiler theorem, and successful runs preserve source
derivations.

This producer receives the witness proof. Type-name freshness, predicate
closedness, the subsequent type-definition command and its equations retain
their separate admission obligations. Native implementation refinement is not
inferred from the finite replay controls.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RegisteredPointedPredicate
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open DefinitionAdapters SignatureFormation ReverseTranslation
attribute [local instance] PointedPredicateTemplate.instDecidablePredSequentEmptyAxiomPolicy

private theorem accepted_at (policy : AxiomPolicy) (first second : DecidablePred policy)
    (proof : @RetainedCompilation.CheckedProof policy first) :
    (@ProofSystem.checker policy second).check
      (@RetainedCompilation.CheckedProof.result policy first proof)
      (@RetainedCompilation.CheckedProof.certificate policy first proof) = true := by
  have equal : first = second := Subsingleton.elim _ _
  cases equal
  exact @RetainedCompilation.CheckedProof.accepted policy first proof

theorem template_result_eq_compiled : PointedPredicateTemplate.result =
    (PointedPredicate.compileWitness PointedPredicateTemplate.property).proof.result := by
  let compiled := PointedPredicate.compileWitness PointedPredicateTemplate.property
  have originalAxioms : compiled.proof.result.axioms = ∅ :=
    axioms_eq_empty_of_emptyAxiomPolicy
      (derives_shared emptyAxiomPolicy ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _
        (accepted_at _ _ _ compiled.proof)))
  apply Theorem.ext
  · exact PointedPredicateTemplate.no_axioms.trans originalAxioms.symm
  · apply Sequent.ext
    · exact PointedPredicateTemplate.no_hypotheses.trans compiled.hypotheses_exact.symm
    · exact PointedPredicateTemplate.exact_conclusion.trans compiled.conclusion_exact.symm

theorem specialized_result_eq {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) :
    substituteTheorem (PointedPredicateInstantiation.specialization property) PointedPredicateTemplate.result =
      (PointedPredicateInstantiation.specializedProof property).result := by
  rw [template_result_eq_compiled]
  rfl

theorem template_nodes_formed (context : TheoryContext)
    (included : ContextControls.coreContext.signature.Includes context.signature) :
    ∀ node ∈ PointedPredicateTemplate.certificate.1,
      ProofExecution.Registered.requestFormedB context.signature
        (ExportReplay.instanceCertificates context.signature) node.witness = true ∧
      theoremFormedB context.signature (ExportReplay.instanceCertificates context.signature) node.conclusion = true := by
  intro node member
  have original := PointedPredicateTemplate.nodes_formed node member
  refine ⟨?_,(TypeInstantiationCertificates.theoremFormedB_exact _ _).mpr
    ((theoremFormedB_sound _ _ original.2).mono included)⟩
  cases request : node.witness with
  | «axiom» statement => rfl
  | inference inference =>
    have old := original.1
    rw [request] at old
    have formed := InferenceFormation.check_sound _ _ inference old
    apply (TypeInstantiationCertificates.inferenceFormationCheck_exact _ _).mpr
    exact ⟨fun type member => (formed.1 type member).mono included,
      fun term member => (formed.2 term member).mono included⟩

theorem specialization_formed {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) (context : TheoryContext)
    (included : ContextControls.coreContext.signature.Includes context.signature)
    (targetFormed : TypeFormed context.signature (reverseTy target))
    (propertyFormed : AnnotationsFormed context.signature
      (reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand property)).term) :
    SubstitutionFormed context.signature (PointedPredicateInstantiation.specialization property) := by
  let expression := reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand property)
  let replacement := PrimitiveTransport.checkedSource expression
  have boolFormed : TypeFormed context.signature Ty.bool :=
    ContextControls.boolean_formed.mono (ContextControls.core_includes.trans included)
  have functionRegistered : context.signature.typeOperators TypeOp.function = some 2 :=
    included.1 _ _ (ContextControls.core_includes.1 _ _ ContextControls.function_registered)
  constructor
  · intro entry member
    change entry ∈ [(PointedPredicateTemplate.alphaName,reverseTy target)] at member
    simp only [List.mem_singleton] at member
    subst entry
    exact targetFormed
  · intro entry member
    change entry ∈ [(⟨PointedPredicateTemplate.propertyVariable.name,reverseTy (.arr target .prop)⟩,replacement)] at member
    simp only [List.mem_singleton] at member
    subst entry
    exact TypeFormed.function _ functionRegistered targetFormed boolFormed
  · intro entry member
    change entry ∈ [(⟨PointedPredicateTemplate.propertyVariable.name,reverseTy (.arr target .prop)⟩,replacement)] at member
    simp only [List.mem_singleton] at member
    subst entry
    change AnnotationsFormed _ (PrimitiveTransport.checkedSource expression).canonical.term
    rw [PrimitiveTransport.checkedSource_exact]
    exact propertyFormed

#print axioms template_result_eq_compiled
#print axioms specialized_result_eq
#print axioms template_nodes_formed
#print axioms specialization_formed

def prepare (context : TheoryContext) : Option ProofExecution.Registered.State :=
  ProofExecution.Registered.replayFrom emptyAxiomPolicy (ProofExecution.Registered.empty context)
    (PointedPredicateTemplate.certificate.1.map fun node =>
      .proof node (ExportReplay.instanceCertificates context.signature))

def replay {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) (context : TheoryContext) :
    Option (ProofExecution.Registered.State × Nat) := do
  let before ← prepare context
  let after ← RegisteredSubstitution.apply emptyAxiomPolicy
    (PointedPredicateInstantiation.specialization property) before PointedPredicateTemplate.certificate.2
    ("pointed-predicate-specialization",0)
  pure (after,before.cache.size+1)

theorem prepare_available (context : TheoryContext)
    (included : ContextControls.coreContext.signature.Includes context.signature) :
    ∃ after, prepare context = some after ∧ after.context = context ∧
      after.cache[PointedPredicateTemplate.certificate.2]? = some PointedPredicateTemplate.result := by
  obtain ⟨cache,native,root⟩ :=
    (ProofSystem.checker_check_iff emptyAxiomPolicy PointedPredicateTemplate.result
      PointedPredicateTemplate.certificate).mp PointedPredicateTemplate.accepted
  obtain ⟨after,received,sameContext,sameCache⟩ :=
    ProofExecution.Registered.replayProofs_available emptyAxiomPolicy
      (ProofExecution.Registered.empty context) PointedPredicateTemplate.certificate.1
      (ExportReplay.instanceCertificates context.signature) cache (template_nodes_formed context included) native
  exact ⟨after,received,sameContext,sameCache ▸ root⟩

theorem replay_available {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) (context : TheoryContext)
    (included : ContextControls.coreContext.signature.Includes context.signature)
    (targetFormed : TypeFormed context.signature (reverseTy target))
    (propertyFormed : AnnotationsFormed context.signature
      (reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand property)).term) :
    ∃ after root, replay property context = some (after,root) ∧ after.context = context ∧
      after.cache[root]? = some (PointedPredicateInstantiation.specializedProof property).result := by
  obtain ⟨before,prepared,sameContext,known⟩ := prepare_available context included
  have inputFormed : TheoremFormed before.context.signature PointedPredicateTemplate.result := by
    rw [sameContext]
    exact PointedPredicateTemplate.result_formed.mono included
  have formed : SubstitutionFormed before.context.signature
      (PointedPredicateInstantiation.specialization property) := by
    rw [sameContext]
    exact specialization_formed property context included targetFormed propertyFormed
  obtain ⟨after,applied,sameAfter,_,root,_⟩ := RegisteredSubstitution.apply_available emptyAxiomPolicy
    (PointedPredicateInstantiation.specialization property) before PointedPredicateTemplate.certificate.2
    ("pointed-predicate-specialization",0) known inputFormed formed
  refine ⟨after,before.cache.size+1,?_,sameAfter.trans sameContext,?_⟩
  · simp [replay,prepared,applied]
  · simpa only [specialized_result_eq] using root

theorem replay_preserves_derivations {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) (context : TheoryContext)
    {after : ProofExecution.Registered.State} {root : Nat}
    (accepted : replay property context = some (after,root)) :
    ProofExecution.Registered.Valid emptyAxiomPolicy after := by
  obtain ⟨before,prepared,rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨result,applied,equal⟩ := Option.bind_eq_some_iff.mp rest
  have same : result = after := congrArg Prod.fst (Option.some.inj equal)
  subst result
  exact RegisteredSubstitution.preserves_derivations emptyAxiomPolicy
    (ProofExecution.Registered.replayFrom_preserves_derivations emptyAxiomPolicy _ _ _
      (ProofExecution.Registered.empty_valid _ _) prepared) applied

#print axioms prepare_available
#print axioms replay_available
#print axioms replay_preserves_derivations

namespace Controls

def emptyProperty := PointedPredicateInstantiation.Controls.falseProperty
def functionProperty := PointedPredicateInstantiation.Controls.functionProperty

theorem boolean_formed : TypeFormed ContextControls.coreContext.signature Ty.bool :=
  ContextControls.boolean_formed.mono ContextControls.core_includes

theorem function_formed : TypeFormed ContextControls.coreContext.signature (Ty.function Ty.bool Ty.bool) :=
  TypeFormed.function _ (ContextControls.core_includes.1 _ _ ContextControls.function_registered)
    boolean_formed boolean_formed

theorem empty_property_formed : AnnotationsFormed ContextControls.coreContext.signature
    (reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand emptyProperty)).term :=
  (TypeInstantiationCertificates.annotationsFormedB_exact _ _).mp (by decide +kernel)

theorem function_property_formed : AnnotationsFormed ContextControls.coreContext.signature
    (reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand functionProperty)).term :=
  (TypeInstantiationCertificates.annotationsFormedB_exact _ _).mp (by decide +kernel)

theorem empty_available : ∃ after root, replay emptyProperty ContextControls.coreContext = some (after,root) ∧
    after.context = ContextControls.coreContext ∧
    after.cache[root]? = some (PointedPredicateInstantiation.specializedProof emptyProperty).result :=
  replay_available emptyProperty ContextControls.coreContext ⟨fun _ _ h => h,fun _ _ h => h⟩
    boolean_formed empty_property_formed

theorem function_available : ∃ after root, replay functionProperty ContextControls.coreContext = some (after,root) ∧
    after.context = ContextControls.coreContext ∧
    after.cache[root]? = some (PointedPredicateInstantiation.specializedProof functionProperty).result :=
  replay_available functionProperty ContextControls.coreContext ⟨fun _ _ h => h,fun _ _ h => h⟩
    function_formed function_property_formed

def unregisteredProperty : HOL.ClosedTerm Symbol (.arr .prop .prop) :=
  .const (.constant ⟨Name.global "unregisteredProperty",.undefined⟩ (Ty.function Ty.bool Ty.bool)
    (by rw [Ty.toHOL_function,Ty.toHOL_bool]))

def verdicts : List (String × Bool) :=
  [("cached-witness/empty-property", (replay emptyProperty ContextControls.coreContext).isSome),
   ("cached-witness/function-carrier", (replay functionProperty ContextControls.coreContext).isSome),
   ("cached-witness/unregistered-property-refused", (replay unregisteredProperty ContextControls.coreContext).isNone),
   ("cached-witness/empty-native-axioms", decide ((PointedPredicateInstantiation.specializedProof emptyProperty).result.axioms = ∅))]


theorem closed_empty_result_eq :
    substituteTheorem (PointedPredicateInstantiation.specialization emptyProperty) PointedPredicateTemplate.result =
      (PointedPredicateInstantiation.specializedProof emptyProperty).result := specialized_result_eq emptyProperty

theorem closed_template_formation : ∀ node ∈ PointedPredicateTemplate.certificate.1,
    ProofExecution.Registered.requestFormedB ContextControls.coreContext.signature
      (ExportReplay.instanceCertificates ContextControls.coreContext.signature) node.witness = true ∧
    theoremFormedB ContextControls.coreContext.signature
      (ExportReplay.instanceCertificates ContextControls.coreContext.signature) node.conclusion = true :=
  template_nodes_formed ContextControls.coreContext ⟨fun _ _ h => h,fun _ _ h => h⟩

theorem closed_specialization_formed : SubstitutionFormed ContextControls.coreContext.signature
    (PointedPredicateInstantiation.specialization emptyProperty) :=
  specialization_formed emptyProperty ContextControls.coreContext ⟨fun _ _ h => h,fun _ _ h => h⟩
    boolean_formed empty_property_formed

theorem closed_prepare : ∃ after, prepare ContextControls.coreContext = some after ∧
    after.context = ContextControls.coreContext ∧
    after.cache[PointedPredicateTemplate.certificate.2]? = some PointedPredicateTemplate.result :=
  prepare_available ContextControls.coreContext ⟨fun _ _ h => h,fun _ _ h => h⟩

/-- A proof-only name for the actual output whose executable availability was proved. -/
noncomputable def emptyRun : ProofExecution.Registered.State × Nat :=
  (Classical.choose empty_available,Classical.choose (Classical.choose_spec empty_available))

theorem emptyRun_received : replay emptyProperty ContextControls.coreContext = some emptyRun :=
  (Classical.choose_spec (Classical.choose_spec empty_available)).1

theorem closed_derivations : ProofExecution.Registered.Valid emptyAxiomPolicy emptyRun.1 :=
  replay_preserves_derivations emptyProperty ContextControls.coreContext emptyRun_received

end Controls
#print axioms Controls.empty_available
#print axioms Controls.function_available
end Mettapedia.Languages.HOLLight.RegisteredPointedPredicate
