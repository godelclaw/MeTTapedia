import Mettapedia.Languages.HOLLight.ProofExecution
import Mettapedia.Languages.HOLLight.ProofSystem

/-!
# Primitive proof graphs and registered source reception

Proof-only reception preserves the theory context and replays the same finite
primitive graph. Conversely, primitive replay together with the actual request
and result formation checks constructs the registered execution. Successful
reception retains exactly the checked root at its source address.

The policy, input cache and instance-finder family are explicit. Declaration
extensions use separate rules. A closed registered reflexivity example supplies
all directions. An undeclared constant separates primitive derivability from
registered reception. Native implementation refinement remains separate.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open DefinitionAdapters SignatureFormation

theorem proof_apply_replay (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {node : Receipt} {instances : InstanceWitnesses}
    (accepted : apply policy before (.proof node instances) = some after) :
    after.context = before.context ∧
      node.replay (ruleWitness policy) before.cache = some after.cache ∧
      requestFormedB before.context.signature instances node.witness = true ∧
      theoremFormedB before.context.signature instances node.conclusion = true := by
  obtain ⟨output,checked,context,cache,_⟩ := apply_result policy accepted
  cases native : node.replay (ruleWitness policy) before.cache with
  | none => simp [Command.check,native] at checked
  | some result =>
    by_cases formed : requestFormedB before.context.signature instances node.witness = true ∧
      theoremFormedB before.context.signature instances node.conclusion = true
    · have same : (⟨before.context,[node.conclusion]⟩ : Output) = output :=
        Option.some.inj (by simpa [Command.check,native,formed] using checked)
      subst output
      have resultShape : result = before.cache.push node.conclusion :=
        DerivationGraph.Node.replay_eq_push (ruleWitness policy) native
      have cacheShape : after.cache = before.cache.push node.conclusion := by
        change after.cache = before.cache ++ #[node.conclusion] at cache
        simpa only [Array.append_singleton] using cache
      exact ⟨context,congrArg some (resultShape.trans cacheShape.symm),formed⟩
    · simp [Command.check,native,formed] at checked

#print axioms proof_apply_replay

theorem replayProofs_primitive (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (nodes : List Receipt) (instances : InstanceWitnesses) {after : State}
    (accepted : replayFrom policy before (nodes.map fun node => .proof node instances) = some after) :
    after.context = before.context ∧
      DerivationGraph.replayFrom (ruleWitness policy) before.cache nodes = some after.cache ∧
      ∀ node ∈ nodes, requestFormedB before.context.signature instances node.witness = true ∧
        theoremFormedB before.context.signature instances node.conclusion = true := by
  induction nodes generalizing before with
  | nil =>
    have equal : before = after := Option.some.inj accepted
    cases equal
    exact ⟨rfl,rfl,by intro node member; cases member⟩
  | cons node nodes ih =>
    cases first : apply policy before (.proof node instances) with
    | none => simp [replayFrom,first] at accepted
    | some middle =>
      have tail : replayFrom policy middle (nodes.map fun node => .proof node instances) = some after := by
        simpa [replayFrom,first] using accepted
      obtain ⟨lastContext,restReplay,restFormed⟩ := ih middle tail
      obtain ⟨firstContext,firstReplay,firstFormed⟩ := proof_apply_replay policy first
      refine ⟨lastContext.trans firstContext,?_,?_⟩
      · simp only [DerivationGraph.replayFrom,firstReplay]
        exact restReplay
      · intro candidate member
        rcases List.mem_cons.mp member with rfl | member
        · exact firstFormed
        · simpa only [firstContext] using restFormed candidate member

theorem replayProofs_available (policy : AxiomPolicy) [DecidablePred policy]
    (before : ProofExecution.Registered.State) (nodes : List ProofExecution.Receipt)
    (instances : InstanceWitnesses) (out : Array Theorem)
    (formed : ∀ node ∈ nodes,
      ProofExecution.Registered.requestFormedB before.context.signature instances node.witness = true ∧
      theoremFormedB before.context.signature instances node.conclusion = true)
    (checked : DerivationGraph.replayFrom (ruleWitness policy) before.cache nodes = some out) :
    ∃ after, ProofExecution.Registered.replayFrom policy before
        (nodes.map (fun node => .proof node instances)) = some after ∧
      after.context = before.context ∧ after.cache = out := by
  induction nodes generalizing before with
  | nil =>
    have same : before.cache = out := Option.some.inj checked
    exact ⟨before, rfl, rfl, same⟩
  | cons node nodes ih =>
    cases first : node.replay (ruleWitness policy) before.cache with
    | none => simp [DerivationGraph.replayFrom, first] at checked
    | some middleCache =>
      have rest : DerivationGraph.replayFrom (ruleWitness policy) middleCache nodes = some out := by
        simpa [DerivationGraph.replayFrom, first] using checked
      have head := formed node (by simp)
      have command : (ProofExecution.Registered.Command.proof node instances).check
          policy before.context before.cache = some ⟨before.context, [node.conclusion]⟩ := by
        simp [ProofExecution.Registered.Command.check, first, head.1, head.2]
      let middle : ProofExecution.Registered.State :=
        ⟨before.context, before.cache ++ #[node.conclusion],
          before.receipts.push ⟨.proof node instances, [node.conclusion]⟩⟩
      have step : ProofExecution.Registered.apply policy before (.proof node instances) = some middle := by
        simp [ProofExecution.Registered.apply, command, middle]
      have cache : middle.cache = middleCache := by
        obtain ⟨_, _, _, same⟩ :=
          (node.replay_eq_some_iff (ruleWitness policy) before.cache middleCache).mp first
        change before.cache ++ #[node.conclusion] = middleCache
        rw [← Array.push_eq_append]
        exact same.symm
      obtain ⟨after, tail, context, result⟩ := ih middle
        (fun next member => formed next (by simp [member])) (cache ▸ rest)
      refine ⟨after, ?_, context, result⟩
      simpa [List.map, ProofExecution.Registered.replayFrom, step] using tail


#print axioms replayProofs_primitive
#print axioms replayProofs_available

theorem replayProofs_iff (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (nodes : List Receipt) (instances : InstanceWitnesses) :
    (∃ after, replayFrom policy before (nodes.map fun node => .proof node instances) = some after) ↔
      (∃ cache, DerivationGraph.replayFrom (ruleWitness policy) before.cache nodes = some cache) ∧
      ∀ node ∈ nodes, requestFormedB before.context.signature instances node.witness = true ∧
        theoremFormedB before.context.signature instances node.conclusion = true := by
  constructor
  · rintro ⟨after,accepted⟩
    obtain ⟨_,native,formed⟩ := replayProofs_primitive policy before nodes instances accepted
    exact ⟨⟨after.cache,native⟩,formed⟩
  · rintro ⟨⟨cache,native⟩,formed⟩
    obtain ⟨after,accepted,_,_⟩ := replayProofs_available policy before nodes instances cache formed native
    exact ⟨after,accepted⟩

theorem replayProofs_root (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) {claim : Theorem} {certificate : ProofSystem.Certificate}
    (instances : InstanceWitnesses) {after : State}
    (checked : (ProofSystem.checker policy).check claim certificate = true)
    (received : replayFrom policy (empty context)
      (certificate.1.map fun node => .proof node instances) = some after) :
    after.context = context ∧ after.cache[certificate.2]? = some claim := by
  obtain ⟨cache,native,root⟩ := (ProofSystem.checker_check_iff policy _ _).mp checked
  obtain ⟨sameContext,actual,_⟩ := replayProofs_primitive policy (empty context) certificate.1 instances received
  have equal : cache = after.cache := Option.some.inj (native.symm.trans actual)
  exact ⟨sameContext,equal ▸ root⟩

#print axioms replayProofs_iff
#print axioms replayProofs_root

namespace GraphControls
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def nodes : List Receipt := [Controls.existenceNode]
def instances : InstanceWitnesses := Controls.certificates

theorem received : replayFrom emptyAxiomPolicy (empty ContextControls.coreContext)
    (nodes.map fun node => .proof node instances) = some Controls.withExistence := by
  change replayFrom emptyAxiomPolicy (empty ContextControls.coreContext)
    [Controls.existenceCommand] = some Controls.withExistence
  simp [replayFrom,Controls.existence_applied]

theorem primitive : DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy) #[] nodes =
    some #[ContextControls.identityExistence] := by
  simp [nodes,DerivationGraph.replayFrom,Controls.existence_replayed]

theorem formed : ∀ node ∈ nodes,
    requestFormedB ContextControls.coreContext.signature instances node.witness = true ∧
      theoremFormedB ContextControls.coreContext.signature instances node.conclusion = true := by
  intro node member
  have equal : node = Controls.existenceNode := by simpa [nodes] using member
  subst node
  exact Controls.existence_formation

theorem closed_primitive : Controls.withExistence.context = ContextControls.coreContext ∧
    DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy) #[] nodes = some Controls.withExistence.cache ∧
    ∀ node ∈ nodes, requestFormedB ContextControls.coreContext.signature instances node.witness = true ∧
      theoremFormedB ContextControls.coreContext.signature instances node.conclusion = true :=
  replayProofs_primitive emptyAxiomPolicy (empty ContextControls.coreContext) nodes instances received

theorem closed_available : ∃ after,
    replayFrom emptyAxiomPolicy (empty ContextControls.coreContext)
      (nodes.map fun node => .proof node instances) = some after ∧
      after.context = ContextControls.coreContext ∧ after.cache = #[ContextControls.identityExistence] :=
  replayProofs_available emptyAxiomPolicy (empty ContextControls.coreContext) nodes instances _ formed primitive

theorem closed_iff :
    (∃ after, replayFrom emptyAxiomPolicy (empty ContextControls.coreContext)
      (nodes.map fun node => .proof node instances) = some after) ↔
    (∃ cache, DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy) #[] nodes = some cache) ∧
      ∀ node ∈ nodes, requestFormedB ContextControls.coreContext.signature instances node.witness = true ∧
        theoremFormedB ContextControls.coreContext.signature instances node.conclusion = true :=
  replayProofs_iff emptyAxiomPolicy (empty ContextControls.coreContext) nodes instances

theorem checked : (ProofSystem.checker emptyAxiomPolicy).check ContextControls.identityExistence (nodes,0) = true :=
  (ProofSystem.checker_check_iff _ _ _).mpr ⟨#[ContextControls.identityExistence],primitive,rfl⟩

theorem closed_root : Controls.withExistence.context = ContextControls.coreContext ∧
    Controls.withExistence.cache[0]? = some ContextControls.identityExistence :=
  replayProofs_root emptyAxiomPolicy ContextControls.coreContext instances checked received


def unregisteredNode : Receipt :=
  ⟨Controls.undeclaredReflexivity,.inference (.refl Controls.undeclaredTerm),[],("undeclared",0)⟩

theorem unregistered_primitive_replay :
    DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy) #[] [unregisteredNode] =
      some #[Controls.undeclaredReflexivity] := by
  have first : unregisteredNode.replay (ruleWitness emptyAxiomPolicy) #[] =
      some #[Controls.undeclaredReflexivity] := by
    apply (ProofSystem.node_replay_iff emptyAxiomPolicy _ _ _).mpr
    exact ⟨rfl,by decide +kernel,rfl⟩
  simp [DerivationGraph.replayFrom,first]

theorem unregistered_reception_refused :
    replayFrom emptyAxiomPolicy (empty ContextControls.coreContext)
      [Command.proof unregisteredNode instances] = none := by
  change replayFrom emptyAxiomPolicy (empty ContextControls.coreContext)
    [Controls.undeclaredCommand] = none
  simp [replayFrom,Controls.undeclared_constant_refused]

end GraphControls
#print axioms GraphControls.closed_primitive
#print axioms GraphControls.closed_available
#print axioms GraphControls.closed_iff
#print axioms GraphControls.closed_root
#print axioms GraphControls.unregistered_primitive_replay
#print axioms GraphControls.unregistered_reception_refused
end Mettapedia.Languages.HOLLight.ProofExecution.Registered
