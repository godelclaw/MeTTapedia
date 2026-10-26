import Mettapedia.Languages.HOLLight.Rules
import Mettapedia.Languages.HOLLight.DefinitionAdapters
import Mettapedia.Logic.DerivationGraph
import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.TypeTheory.ExtensionalReadout

/-!
# Source-derived HOL Light proof execution

One transition replays a source rule against previously stored premises and
retains its receipt. Proof graph references retain ordered premise occurrences
and shared dependencies. The execution policy may select the next candidate;
it does not authorize an unproved theorem.

The support reading forgets receipts. Its observer criterion is the existing
extensional-readout law. The controls below are actual admitted executions;
they distinguish support from origin and proof-building cost.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ProofExecution

open Mettapedia.Languages.OpenTheory Mettapedia.Logic Mettapedia.GSLT
open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

abbrev Origin := String × Nat
abbrev Receipt := DerivationGraph.Node Theorem RuleRequest Origin

structure State where
  cache : Array Theorem
  receipts : Array Receipt

def empty : State := ⟨#[], #[]⟩

def Step (policy : AxiomPolicy) [DecidablePred policy] (before after : State) : Prop :=
  ∃ receipt : Receipt,
    receipt.replay (ruleWitness policy) before.cache = some after.cache ∧
      after.receipts = before.receipts.push receipt

/-- The transition is computed by the source-rule replay interface; the
equations currently retain complete states and therefore complete receipts. -/
def gslt (policy : AxiomPolicy) [DecidablePred policy] : GSLT :=
  equalityGSLT State (Step policy)

def Valid (policy : AxiomPolicy) (state : State) : Prop :=
  ∀ fact ∈ state.cache, Derives (Rule policy) fact

theorem empty_valid (policy : AxiomPolicy) : Valid policy empty := by
  intro fact member
  simp [empty] at member

theorem step_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} (step : Step policy before after) (valid : Valid policy before) :
    Valid policy after := by
  obtain ⟨receipt, replayed, _⟩ := step
  exact receipt.replay_sound (ruleWitness policy) valid replayed

private theorem multiStep_preserves {system : GSLT} {invariant : system.Term → Prop}
    (stable : ∀ {before after}, system.Step before after → invariant before → invariant after)
    {before after : system.Term} : system.MultiStep before after →
      invariant before → invariant after
  | .refl _, valid => valid
  | .step first rest, valid => multiStep_preserves stable rest (stable first valid)

/-- Every reachable stored theorem has a source derivation, under precisely
the selected object-theory policy. -/
theorem reachable_source_derivation (policy : AxiomPolicy) [DecidablePred policy]
    {after : State} (path : (gslt policy).MultiStep empty after) : Valid policy after := by
  exact multiStep_preserves (system := gslt policy)
    (step_preserves_derivations policy) path (empty_valid policy)

/-- Execution reachability supplies actual shared-STT derivations. -/
theorem reachable_shared_derivation (policy : AxiomPolicy) [DecidablePred policy]
    {after : State} (path : (gslt policy).MultiStep empty after)
    {fact : Theorem} (present : fact ∈ after.cache) :
    Derives (PolicyPrimitiveRule policy) fact :=
  derives_shared policy (reachable_source_derivation policy path fact present)

/-- Every accepted finite proof graph is executable, with all graph nodes
retained as receipts. This does not reconstruct receipts from support. -/
theorem replayFrom_reachable (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (nodes : List Receipt) (result : Array Theorem)
    (accepted : DerivationGraph.replayFrom (ruleWitness policy) before.cache nodes = some result) :
    ∃ receipts, (gslt policy).MultiStep before ⟨result, receipts⟩ := by
  induction nodes generalizing before with
  | nil =>
      obtain ⟨cache, receipts⟩ := before
      cases Option.some.inj accepted
      exact ⟨receipts, .refl _⟩
  | cons node rest ih =>
      cases first : node.replay (ruleWitness policy) before.cache with
      | none => simp [DerivationGraph.replayFrom, first] at accepted
      | some cache =>
          let next : State := ⟨cache, before.receipts.push node⟩
          have remaining :
              DerivationGraph.replayFrom (ruleWitness policy) next.cache rest = some result := by
            simpa [DerivationGraph.replayFrom, first, next] using accepted
          obtain ⟨receipts, path⟩ := ih next remaining
          exact ⟨receipts, .step ⟨node, first, rfl⟩ path⟩

/-- Logical derivability and finite proof-building reachability coincide.
No scheduler fairness or physical storage guarantee is inferred from this
existence theorem. The reachable states retain their actual proof receipts. -/
theorem derives_iff_reachable (policy : AxiomPolicy) [DecidablePred policy] (fact : Theorem) :
    Derives (Rule policy) fact ↔
      ∃ after, (gslt policy).MultiStep empty after ∧ fact ∈ after.cache := by
  constructor
  · intro derivation
    obtain ⟨nodes, cache, index, accepted, found⟩ :=
      DerivationGraph.exists_replay_of_derives (ruleWitness policy) ("authored", 0) derivation
    obtain ⟨receipts, path⟩ := replayFrom_reachable policy empty nodes cache accepted
    exact ⟨⟨cache, receipts⟩, path, Array.mem_of_getElem? found⟩
  · rintro ⟨after, path, present⟩
    exact reachable_source_derivation policy path fact present

/-- This native OSLF type asks whether finite proof construction can reach a
state containing the requested theorem. Primitive step observations remain a
different interface from this reachability-scale modality. -/
def theoremNativeType (policy : AxiomPolicy) [DecidablePred policy] (fact : Theorem) :
    GSLTNativeType (gslt policy).closure where
  sort := ()
  pred := semanticDiamond (gslt policy).closure
    ⟨fun state => fact ∈ state.cache, by
      intro left right same
      change left = right at same
      cases same
      rfl⟩

/-- The existing OSLF construction observes exactly the source derivability
judgment at the stated reachability readout. -/
theorem satisfies_theoremNativeType_iff (policy : AxiomPolicy) [DecidablePred policy]
    (fact : Theorem) :
    (gsltOSLF (gslt policy).closure).satisfies (S := ()) empty
      (theoremNativeType policy fact).pred ↔ Derives (Rule policy) fact := by
  constructor
  · intro observed
    obtain ⟨after, ⟨reached, path, same⟩, present⟩ :=
      (gsltDiamond_spec (gslt policy).closure (fun state : State => fact ∈ state.cache) empty).mp observed
    change reached = after at same
    cases same
    exact reachable_source_derivation policy path fact present
  · intro proof
    obtain ⟨after, path, present⟩ := (derives_iff_reachable policy fact).mp proof
    exact (gsltDiamond_spec (gslt policy).closure
      (fun state : State => fact ∈ state.cache) empty).mpr ⟨after, ⟨after, path, rfl⟩, present⟩

/-- Receipt requirements are also legitimate native predicates before any
extensional support quotient is applied. -/
def receiptNativeType (policy : AxiomPolicy) [DecidablePred policy]
    (origin : Origin) : GSLTNativeType (gslt policy) where
  sort := ()
  pred := ⟨fun state => ∃ receipt ∈ state.receipts.toList, receipt.origin = origin, by
    intro left right same
    change left = right at same
    cases same
    rfl⟩

def support (state : State) : Finset Sequent :=
  (state.cache.toList.map Theorem.sequent).toFinset

def cost (state : State) : Nat := state.receipts.size

/-- A dependent consumer requests a receipt with a particular retained
origin. Its witness is the receipt itself, rather than a Boolean verdict. -/
def ReceiptAtOrigin (state : State) (origin : Origin) : Type :=
  {receipt : Receipt // receipt ∈ state.receipts.toList ∧ receipt.origin = origin}

def consumeOrigin {state : State} {origin : Origin} (evidence : ReceiptAtOrigin state origin) :
    {received : Origin // received = evidence.val.origin} :=
  ⟨evidence.val.origin, rfl⟩

/-- Only actual reachable states enter this qualified support readout. -/
abbrev ReachableState (policy : AxiomPolicy) [DecidablePred policy] :=
  {state : State // (gslt policy).MultiStep empty state}

def SupportImage (policy : AxiomPolicy) [DecidablePred policy] :=
  Set.range (fun state : ReachableState policy => support state.val)

noncomputable def supportReadout (policy : AxiomPolicy) [DecidablePred policy] :
    SplitReadout (ReachableState policy) (SupportImage policy) where
  observe state := ⟨support state.val, ⟨state, rfl⟩⟩
  representative target := Classical.choose target.property
  observe_representative target := by
    apply Subtype.ext
    exact Classical.choose_spec target.property

/-- The choice of a representative is a mathematical section, not a native
procedure for recovering evidence from a merely observed fact set. -/
theorem support_observer_descends_iff (policy : AxiomPolicy) [DecidablePred policy]
    {Observation : Type} (observer : ReachableState policy → Observation) :
    (supportReadout policy).FactorsObserver observer ↔
      (supportReadout policy).FibreInvariant observer :=
  (supportReadout policy).factorsObserver_iff_fibreInvariant observer

namespace Controls

instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse (fun impossible => impossible)

def proposition : CanonicalTerm := CanonicalTerm.free ⟨.global "p", Ty.bool⟩
def equality := CanonicalTerm.equalityOfSameType proposition proposition rfl
def reflexivityTheorem : Theorem := Theorem.emptyResult ∅ equality

def reflexivity (origin : Origin) : Receipt :=
  ⟨reflexivityTheorem, .inference (.refl proposition), [], origin⟩

def once (origin : Origin) : State := ⟨#[reflexivityTheorem], #[reflexivity origin]⟩

theorem reflexivity_replayed (origin : Origin) :
    (reflexivity origin).replay (ruleWitness emptyAxiomPolicy) #[] = some #[reflexivityTheorem] := by
  have checked : checkRefl proposition = some reflexivityTheorem :=
    (checkRefl_eq_some_iff _ _).mpr
      ⟨equality, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩
  have admitted :
      (RuleRequest.inference (.refl proposition)).isInstance emptyAxiomPolicy []
        reflexivityTheorem = true :=
    (RuleRequest.isInstance_eq_true_iff _ _ _ _).mpr
      ⟨rfl, (checkRefl_eq_some_iff _ _).mp checked⟩
  simp [reflexivity, DerivationGraph.Node.replay, DerivationGraph.lookupPremises,
    ruleWitness, admitted]

theorem once_reachable (origin : Origin) : (gslt emptyAxiomPolicy).MultiStep empty (once origin) := by
  apply GSLT.MultiStep.step (u := once origin)
  · exact ⟨reflexivity origin, reflexivity_replayed origin, rfl⟩
  · exact .refl _

theorem origins_same_support (first second : Origin) : support (once first) = support (once second) := rfl

theorem retained_origin_available (origin : Origin) : Nonempty (ReceiptAtOrigin (once origin) origin) :=
  ⟨⟨reflexivity origin, by simp [once], rfl⟩⟩

theorem different_origin_refused {first second : Origin} (different : first ≠ second) :
    ¬ Nonempty (ReceiptAtOrigin (once first) second) := by
  rintro ⟨⟨receipt, member, selected⟩⟩
  have equal : receipt = reflexivity first := by simpa [once] using member
  exact different (by simpa [equal, reflexivity] using selected)

/-- One source theorem is cited twice, rather than replaced by two independent
proofs. The graph and the consumer retain those two uses of one origin. -/
def sharedTransitivity (origin : Origin) : Receipt :=
  ⟨reflexivityTheorem, .inference (.trans reflexivityTheorem reflexivityTheorem), [0, 0], origin⟩

def twice (first second : Origin) : State :=
  ⟨#[reflexivityTheorem, reflexivityTheorem],
    #[reflexivity first, sharedTransitivity second]⟩

theorem shared_transitivity_replayed (first second : Origin) :
    (sharedTransitivity second).replay (ruleWitness emptyAxiomPolicy) (once first).cache =
      some (twice first second).cache := by
  have semantics : TransSemantics reflexivityTheorem reflexivityTheorem reflexivityTheorem := by
    refine ⟨proposition, proposition, proposition, proposition, equality,
      ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
      CanonicalTerm.equalityOfSameType_semantics _ _ rfl, ?_⟩
    simp [HasParts, reflexivityTheorem, Theorem.emptyResult]
  have admitted :
      (RuleRequest.inference (.trans reflexivityTheorem reflexivityTheorem)).isInstance
        emptyAxiomPolicy [reflexivityTheorem, reflexivityTheorem] reflexivityTheorem = true :=
    (RuleRequest.isInstance_eq_true_iff _ _ _ _).mpr ⟨rfl, semantics⟩
  simp [once, twice, sharedTransitivity, DerivationGraph.Node.replay,
    DerivationGraph.lookupPremises, ruleWitness, admitted]

theorem twice_reachable (first second : Origin) :
    (gslt emptyAxiomPolicy).MultiStep empty (twice first second) := by
  apply GSLT.MultiStep.step (u := once first)
  · exact ⟨reflexivity first, reflexivity_replayed first, rfl⟩
  · exact .step ⟨sharedTransitivity second, shared_transitivity_replayed first second, rfl⟩
      (.refl _)

theorem one_origin_two_premise_uses (origin : Origin) :
    DerivationGraph.lookupPremises (once origin).cache
      (sharedTransitivity origin).parents = some [reflexivityTheorem, reflexivityTheorem] := rfl

theorem extra_inference_same_support (first second : Origin) :
    support (once first) = support (twice first second) := by
  simp [support, once, twice]

theorem extra_inference_changes_cost (first second : Origin) :
    cost (once first) ≠ cost (twice first second) := by
  change (1 : Nat) ≠ 2
  decide

/-- An origin-indexed evidence consumer cannot descend to support. -/
theorem origin_observer_does_not_descend :
    ¬ (supportReadout emptyAxiomPolicy).FactorsObserver
      (fun state => Nonempty (ReceiptAtOrigin state.val ("source", 0))) := by
  intro factored
  have equal : Nonempty (ReceiptAtOrigin (once ("source", 0)) ("source", 0)) =
      Nonempty (ReceiptAtOrigin (once ("other", 0)) ("source", 0)) :=
    (support_observer_descends_iff _ _).mp factored
      (left := ⟨once ("source", 0), once_reachable _⟩)
      (right := ⟨once ("other", 0), once_reachable _⟩) rfl
  have available := retained_origin_available ("source", 0)
  have absent := different_origin_refused (first := ("other", 0))
    (second := ("source", 0)) (by decide)
  exact absent (equal ▸ available)

/-- Proof-building cost also distinguishes two reachable executions with the
same support. This is not a claim about physical running time. -/
theorem cost_observer_does_not_descend :
    ¬ (supportReadout emptyAxiomPolicy).FactorsObserver
      (fun state => cost state.val) := by
  intro factored
  have same : (supportReadout emptyAxiomPolicy).observe
      ⟨once ("source", 0), once_reachable _⟩ =
      (supportReadout emptyAxiomPolicy).observe
      ⟨twice ("source", 0) ("trans", 1), twice_reachable _ _⟩ := by
    apply Subtype.ext
    exact extra_inference_same_support _ _
  exact extra_inference_changes_cost _ _
    ((support_observer_descends_iff _ _).mp factored same)

end Controls

/-! ## Execution with registered declarations and definitions

This extension reuses the same graph nodes and source inference checker.
It adds the changing declaration context and definition commands. A type
definition cites an earlier cache address; an unproved theorem record cannot
serve as its existence premise. Each command keeps one ordered receipt,
including the two outputs of a type definition.
-/

theorem replay_policy_congr (first second : AxiomPolicy) [DecidablePred first] [DecidablePred second]
    (node : Receipt) (cache : Array Theorem)
    (agree : ∀ sequent, node.witness.requestedAxiom = some sequent → (first sequent ↔ second sequent)) :
    node.replay (ruleWitness first) cache = node.replay (ruleWitness second) cache := by
  simp only [DerivationGraph.Node.replay,ruleWitness,RuleRequest.isInstance,RuleRequest.outputSameB,
    RuleRequest.check_policy_congr first second node.witness agree]
  rfl

namespace Registered

open DefinitionAdapters OpenTheory.SignatureFormation

inductive Command where
  | proof (node : Receipt) (witnesses : InstanceWitnesses)
  | constant (origin : Origin) (name : Name) (body : SourceTerm) (witnesses : InstanceWitnesses)
  | typeDefinition (origin : Origin) (request : TypeOperatorDefinitionRequest)
      (existenceIndex : Nat) (witnesses : InstanceWitnesses)

def Command.origin : Command → Origin
  | .proof node _ => node.origin
  | .constant origin _ _ _ | .typeDefinition origin _ _ _ => origin

/-- Premise occurrences retain their cache addresses, including duplicates. -/
def Command.parents : Command → List Nat
  | .proof node _ => node.parents
  | .constant _ _ _ _ => []
  | .typeDefinition _ _ index _ => [index]

structure Output where
  context : TheoryContext
  theorems : List Theorem

def requestFormedB (signature : SignatureFormation.Signature)
    (witnesses : InstanceWitnesses) : RuleRequest → Bool
  | .inference request => InferenceFormation.check signature witnesses request
  | .axiom _ => true

/-- The existing graph replay decides every inference. Declaration checks
validate its extra parameters and output in the current theory. -/
def Command.check (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) (cache : Array Theorem) : Command → Option Output
  | .proof node witnesses => do
      let _ ← node.replay (ruleWitness policy) cache
      if requestFormedB context.signature witnesses node.witness = true ∧
          theoremFormedB context.signature witnesses node.conclusion = true then
        pure ⟨context, [node.conclusion]⟩
      else none
  | .constant _ name body witnesses => do
      let result ← admitConstantInTheory context witnesses name body
      if theoremFormedB result.context.signature witnesses result.output.definitionTheorem then
        pure ⟨result.context, [result.output.definitionTheorem]⟩
      else none
  | .typeDefinition _ request index witnesses => do
      let existence ← cache[index]?
      if existence.structuralSame request.existence then
        let result ← admitSourceTypeInTheory context witnesses request
        if theoremFormedB result.context.signature witnesses
            result.output.abstractionRepresentationTheorem = true ∧
            theoremFormedB result.context.signature witnesses
              result.output.representationAbstractionTheorem = true then
          pure ⟨result.context, [result.output.abstractionRepresentationTheorem,
            result.output.representationAbstractionTheorem]⟩
        else none
      else none

/-- Every admitted registered inference has a checking certificate, provided
its actual ordered premises are already in the cache. Definition commands
have their separate ingress and history obligations. -/
theorem Command.check_proof_complete (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) (cache : Array Theorem) (node : Receipt)
    (found : DerivationGraph.lookupPremises cache node.parents = some node.witness.premises)
    (step : node.witness.Semantics policy node.conclusion)
    (argumentsFormed : ∀ request, node.witness = .inference request →
      InferenceFormation.Formed context.signature request)
    (outputFormed : TheoremFormed context.signature node.conclusion) :
    ∃ witnesses : InstanceWitnesses,
      (Command.proof node witnesses).check policy context cache =
        some ⟨context, [node.conclusion]⟩ := by
  obtain ⟨witnesses, realizes⟩ := exists_instanceWitnesses context.signature
  have instanceChecked := (RuleRequest.isInstance_eq_true_iff policy _ _ _).mpr ⟨rfl, step⟩
  have replayed : node.replay (ruleWitness policy) cache = some (cache.push node.conclusion) :=
    (node.replay_eq_some_iff (ruleWitness policy) cache _).mpr
      ⟨node.witness.premises, found, instanceChecked, rfl⟩
  have parameters : requestFormedB context.signature witnesses node.witness = true := by
    cases request : node.witness with
    | inference inference =>
        exact InferenceFormation.check_complete _ _ realizes (argumentsFormed inference request)
    | «axiom» sequent => rfl
  have output := theoremFormedB_complete context.signature witnesses realizes outputFormed
  refine ⟨witnesses, ?_⟩
  simp [Command.check, replayed, parameters, output]

/-- Every successful command extends the old signature and constructs
registered source derivations from the actual cached premises. -/
theorem Command.check_sound (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) (cache : Array Theorem)
    (earlier : ∀ fact ∈ cache, TheoryDerives policy context fact)
    {command : Command} {result : Output}
    (accepted : command.check policy context cache = some result) :
    context.signature.Includes result.context.signature ∧
      ∀ fact ∈ result.theorems, TheoryDerives policy result.context fact := by
  cases command with
  | proof node witnesses =>
      simp only [Command.check] at accepted
      cases replayed : node.replay (ruleWitness policy) cache with
      | none => simp [replayed] at accepted
      | some next =>
          simp only [replayed] at accepted
          split at accepted
          · rename_i formation
            have equal := Option.some.inj accepted
            subst result
            obtain ⟨premises, found, checked, _⟩ :=
              (node.replay_eq_some_iff (ruleWitness policy) cache next).mp replayed
            have sourceCheck : node.witness.isInstance policy premises node.conclusion = true := checked
            obtain ⟨samePremises, sourceStep⟩ :=
              (RuleRequest.isInstance_eq_true_iff policy _ _ _).mp sourceCheck
            have outputFormed := theoremFormedB_sound context.signature witnesses formation.2
            have proof : TheoryDerives policy context node.conclusion := by
              cases source : node.witness with
              | inference request =>
                  rw [source] at samePremises sourceStep formation
                  refine .inference sourceStep
                    (InferenceFormation.check_sound _ _ _ formation.1) ?_ outputFormed
                  intro premise member
                  exact earlier premise
                    (DerivationGraph.lookupPremises_mem cache found premise (samePremises ▸ member))
              | «axiom» sequent =>
                  rw [source] at sourceStep
                  exact .axiom sourceStep.1 sourceStep.2.1 sourceStep.2.2 outputFormed
            exact ⟨.refl _, fun fact member => by simpa using (List.mem_singleton.mp member) ▸ proof⟩
          · contradiction
  | constant origin name body witnesses =>
      simp only [Command.check] at accepted
      cases admitted : admitConstantInTheory context witnesses name body with
      | none => simp [admitted] at accepted
      | some defined =>
          rw [admitted] at accepted
          change (if theoremFormedB defined.context.signature witnesses
            defined.output.definitionTheorem then
              some (⟨defined.context, [defined.output.definitionTheorem]⟩ : Output)
            else none) = some result at accepted
          split at accepted
          · rename_i formed
            have equal := Option.some.inj accepted
            subst result
            have proof := TheoryDerives.constantDefinition (policy := policy) admitted
              (theoremFormedB_sound _ _ formed)
            exact ⟨(admitConstantInTheory_result admitted).2.2.1,
              fun fact member => by simpa using (List.mem_singleton.mp member) ▸ proof⟩
          · contradiction
  | typeDefinition origin request index witnesses =>
      simp only [Command.check] at accepted
      cases found : cache[index]? with
      | none => simp [found] at accepted
      | some existence =>
          rw [found] at accepted
          change (if existence.structuralSame request.existence then do
            let defined ← admitSourceTypeInTheory context witnesses request
            if theoremFormedB defined.context.signature witnesses
                defined.output.abstractionRepresentationTheorem = true ∧
                theoremFormedB defined.context.signature witnesses
                  defined.output.representationAbstractionTheorem = true then
              pure (⟨defined.context, [defined.output.abstractionRepresentationTheorem,
                defined.output.representationAbstractionTheorem]⟩ : Output)
            else none
          else none) = some result at accepted
          split at accepted
          · rename_i sameExistence
            have actual : existence = request.existence :=
              (Theorem.structuralSame_eq_true_iff _ _).mp sameExistence
            have existenceProof := earlier request.existence
              (actual ▸ Array.mem_of_getElem? found)
            cases admitted : admitSourceTypeInTheory context witnesses request with
            | none => simp [admitted] at accepted
            | some defined =>
                rw [admitted] at accepted
                change (if theoremFormedB defined.context.signature witnesses
                    defined.output.abstractionRepresentationTheorem = true ∧
                    theoremFormedB defined.context.signature witnesses
                      defined.output.representationAbstractionTheorem = true then
                  some (⟨defined.context, [defined.output.abstractionRepresentationTheorem,
                    defined.output.representationAbstractionTheorem]⟩ : Output)
                else none) = some result at accepted
                split at accepted
                · rename_i formation
                  have equal := Option.some.inj accepted
                  subst result
                  refine ⟨(admitSourceTypeInTheory_result admitted).1, ?_⟩
                  intro fact member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact .typeAbstractionDefinition admitted existenceProof
                      (theoremFormedB_sound _ _ formation.1)
                  · have equal := List.mem_singleton.mp member
                    subst fact
                    exact .typeRepresentationDefinition admitted existenceProof
                      (theoremFormedB_sound _ _ formation.2)
                · contradiction
          · contradiction

structure CommandReceipt where
  command : Command
  outputs : List Theorem

structure State where
  context : TheoryContext
  cache : Array Theorem
  receipts : Array CommandReceipt

def empty (context : TheoryContext) : State := ⟨context, #[], #[]⟩

def apply (policy : AxiomPolicy) [DecidablePred policy] (before : State)
    (command : Command) : Option State := do
  let result ← command.check policy before.context before.cache
  pure ⟨result.context, before.cache ++ result.theorems.toArray,
    before.receipts.push ⟨command, result.theorems⟩⟩

/-- Cache extension and the retained receipt describe the actual same
command. A multi-output definition occupies consecutive cache positions. -/
theorem apply_result (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {command : Command}
    (accepted : apply policy before command = some after) :
    ∃ result, command.check policy before.context before.cache = some result ∧
      after.context = result.context ∧
      after.cache = before.cache ++ result.theorems.toArray ∧
      after.receipts = before.receipts.push ⟨command, result.theorems⟩ := by
  unfold apply at accepted
  cases checked : command.check policy before.context before.cache with
  | none => simp [checked] at accepted
  | some result =>
      have equal :
          (⟨result.context, before.cache ++ result.theorems.toArray,
            before.receipts.push ⟨command, result.theorems⟩⟩ : State) = after := by
        simpa [checked] using accepted
      subst after
      exact ⟨result, rfl, rfl, rfl, rfl⟩

/-- Definition extension cannot change an existing proof address. Sharing
and repeated premise references therefore survive theory growth. -/
theorem apply_preserves_lookup (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {command : Command}
    (accepted : apply policy before command = some after)
    {index : Nat} {fact : Theorem} (found : before.cache[index]? = some fact) :
    after.cache[index]? = some fact := by
  obtain ⟨_, _, _, cache, _⟩ := apply_result policy accepted
  rw [cache, Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp found).1]
  exact found

def Valid (policy : AxiomPolicy) (state : State) : Prop :=
  ∀ fact ∈ state.cache, TheoryDerives policy state.context fact

theorem empty_valid (policy : AxiomPolicy) (context : TheoryContext) :
    Valid policy (empty context) := by
  intro fact member
  simp [empty] at member

theorem apply_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {command : Command} (valid : Valid policy before)
    (accepted : apply policy before command = some after) : Valid policy after := by
  unfold apply at accepted
  cases checked : command.check policy before.context before.cache with
  | none => simp [checked] at accepted
  | some result =>
      have equal :
          (⟨result.context, before.cache ++ result.theorems.toArray,
            before.receipts.push ⟨command, result.theorems⟩⟩ : State) = after := by
        simpa [checked] using accepted
      subst after
      have preserved := Command.check_sound policy before.context before.cache valid checked
      intro fact member
      rcases Array.mem_append.mp member with previous | new
      · exact .weaken preserved.1 (valid fact previous)
      · exact preserved.2 fact (by simpa using new)

def Step (policy : AxiomPolicy) [DecidablePred policy] (before after : State) : Prop :=
  ∃ command, apply policy before command = some after

def gslt (policy : AxiomPolicy) [DecidablePred policy] : GSLT :=
  equalityGSLT State (Step policy)

/-- Every reachable theorem belongs to the registered source calculus,
including the actual definition rules and their checked existence premises. -/
theorem reachable_source_derivation (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) {after : State}
    (path : (gslt policy).MultiStep (empty context) after) : Valid policy after := by
  apply multiStep_preserves (system := gslt policy) (invariant := Valid policy) ?_ path
    (empty_valid policy context)
  intro before after ⟨command, accepted⟩ valid
  exact apply_preserves_derivations policy valid accepted

theorem reachable_authorized_axioms (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) {after : State}
    (path : (gslt policy).MultiStep (empty context) after)
    {fact : Theorem} (present : fact ∈ after.cache) : policy.AllowsTheorem fact :=
  (reachable_source_derivation policy context path fact present).authorizedAxioms

/-- Replay an arbitrary finite history, including declaration extensions.
Each command is checked once against its actual preceding cache. -/
def replayFrom (policy : AxiomPolicy) [DecidablePred policy] :
    State → List Command → Option State
  | before, [] => some before
  | before, command :: rest => do
      let next ← apply policy before command
      replayFrom policy next rest

theorem replayFrom_reachable (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (commands : List Command) (after : State)
    (accepted : replayFrom policy before commands = some after) :
    (gslt policy).MultiStep before after := by
  induction commands generalizing before with
  | nil =>
      have equal : before = after := Option.some.inj accepted
      subst after
      exact .refl _
  | cons command rest ih =>
      cases checked : apply policy before command with
      | none => simp [replayFrom, checked] at accepted
      | some next =>
          have tail : replayFrom policy next rest = some after := by
            simpa [replayFrom, checked] using accepted
          exact .step ⟨command, checked⟩ (ih next tail)

/-- General finite histories preserve source derivations. This is a theorem
about the admitted calculus and its execution relation, independent of an
agenda choosing the history. -/
theorem replayFrom_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (commands : List Command) (after : State)
    (valid : Valid policy before)
    (accepted : replayFrom policy before commands = some after) : Valid policy after := by
  apply multiStep_preserves (system := gslt policy) (invariant := Valid policy) ?_
    (replayFrom_reachable policy before commands after accepted) valid
  intro first second ⟨command, checked⟩ current
  exact apply_preserves_derivations policy current checked

/-- An accepted history preserves every old address, even through commands
that append two definition results at once. -/
theorem replayFrom_preserves_lookup (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (commands : List Command) (after : State)
    (accepted : replayFrom policy before commands = some after)
    {index : Nat} {fact : Theorem} (found : before.cache[index]? = some fact) :
    after.cache[index]? = some fact := by
  induction commands generalizing before with
  | nil =>
      have equal : before = after := Option.some.inj accepted
      exact equal ▸ found
  | cons command rest ih =>
      cases checked : apply policy before command with
      | none => simp [replayFrom, checked] at accepted
      | some next =>
          have tail : replayFrom policy next rest = some after := by
            simpa [replayFrom, checked] using accepted
          exact ih next tail (apply_preserves_lookup policy checked found)

/-- The native OSLF type observes finite reachability in the registered
execution, including its changing theory and definition receipts. -/
def theoremNativeType (policy : AxiomPolicy) [DecidablePred policy] (fact : Theorem) :
    GSLTNativeType (gslt policy).closure where
  sort := ()
  pred := semanticDiamond (gslt policy).closure
    ⟨fun state => fact ∈ state.cache, by
      intro first second same
      change first = second at same
      cases same
      rfl⟩

/-- This readout asserts exactly its stated reachability scale. It does not
claim that arbitrary declared-theory derivations are already complete for the
chosen initial execution context. -/
theorem satisfies_theoremNativeType_iff_reachable
    (policy : AxiomPolicy) [DecidablePred policy] (context : TheoryContext) (fact : Theorem) :
    (gsltOSLF (gslt policy).closure).satisfies (S := ()) (empty context)
        (theoremNativeType policy fact).pred ↔
      ∃ after, (gslt policy).MultiStep (empty context) after ∧ fact ∈ after.cache := by
  constructor
  · intro observed
    obtain ⟨after, ⟨reached, path, same⟩, present⟩ :=
      (gsltDiamond_spec (gslt policy).closure (fun state : State => fact ∈ state.cache)
        (empty context)).mp observed
    change reached = after at same
    cases same
    exact ⟨after, path, present⟩
  · rintro ⟨after, path, present⟩
    exact (gsltDiamond_spec (gslt policy).closure (fun state : State => fact ∈ state.cache)
      (empty context)).mpr ⟨after, ⟨after, path, rfl⟩, present⟩

namespace Controls

open DefinitionAdapters.ContextControls

instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse (fun impossible => impossible)

/-- Equality instances can have several operand types in one proof. Other
symbols in this control have monomorphic declaration schemas. -/
def certificates : InstanceWitnesses := fun constant annotation =>
  if Const.same constant Const.equality then
    match annotation.destFunction? with
    | some (operand, _) => ⟨[(equalityParameter, operand)]⟩
    | none => TypeSubst.empty
  else TypeSubst.empty

def existenceNode : Receipt :=
  ⟨identityExistence, .inference (.refl DefinitionAdapters.Controls.identityTerm), [], ("refl", 0)⟩

def existenceCommand : Command := .proof existenceNode certificates

theorem existence_replayed :
    existenceNode.replay (ruleWitness emptyAxiomPolicy) #[] = some #[identityExistence] := by
  have admitted : existenceNode.witness.isInstance emptyAxiomPolicy [] identityExistence = true :=
    (RuleRequest.isInstance_eq_true_iff _ _ _ _).mpr
      ⟨rfl, ⟨_, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩⟩
  change (RuleRequest.inference (.refl DefinitionAdapters.Controls.identityTerm)).isInstance
    emptyAxiomPolicy [] identityExistence = true at admitted
  simp [existenceNode, DerivationGraph.Node.replay, DerivationGraph.lookupPremises,
    ruleWitness, admitted]

theorem existence_formation :
    requestFormedB coreContext.signature certificates existenceNode.witness = true ∧
      theoremFormedB coreContext.signature certificates identityExistence = true := by
  simp [requestFormedB, InferenceFormation.check, InferenceFormation.types,
    InferenceFormation.terms, theoremFormedB, sequentFormedB, existenceNode,
    identityExistence, Theorem.emptyResult, CanonicalTerm.equalityOfSameType,
    CanonicalTerm.equalityDB, DefinitionAdapters.Controls.identityTerm,
    annotationsFormedB, typeFormedB, constantInstanceB, coreContext, baseContext,
    booleanContext, TheoryContext.addConstant, TheoryContext.addTypeOperator,
    TheoryContext.empty, Signature.addConstant, Signature.addTypeOperator,
    certificates, equalityParameter, Const.equality, TypeOp.bool, TypeOp.function,
    Ty.equality, Ty.function, Ty.bool, Const.same, TypeOp.same,
    TypeSubst.lookup, Ty.destFunction?, Name.global]

def withExistence : State :=
  ⟨coreContext, #[identityExistence], #[⟨existenceCommand, [identityExistence]⟩]⟩

theorem existence_applied :
    apply emptyAxiomPolicy (empty coreContext) existenceCommand = some withExistence := by
  simp only [apply, Command.check, empty, existenceCommand, existence_replayed]
  change ((if requestFormedB coreContext.signature certificates existenceNode.witness = true ∧
        theoremFormedB coreContext.signature certificates identityExistence = true then
      some (⟨coreContext, [identityExistence]⟩ : Output) else none).bind
    (fun result => some (⟨result.context, #[] ++ result.theorems.toArray,
      #[⟨existenceCommand, result.theorems⟩]⟩ : State))) = some withExistence
  rw [if_pos existence_formation]
  rfl

theorem existence_checked :
    (apply emptyAxiomPolicy (empty coreContext) existenceCommand).isSome = true := by
  rw [existence_applied]
  rfl

theorem withExistence_valid : Valid emptyAxiomPolicy withExistence := by
  apply apply_preserves_derivations emptyAxiomPolicy (empty_valid _ _)
  exact existence_applied

def typeCommand : Command := .typeDefinition ("define-type", 1) identityTypeRequest 0 certificates

def definedCore : ContextTypeDefinitionResult :=
  { context := coreContext.typeDefinitionExtension identityTypeRequest
      DefinitionAdapters.Controls.identityTerm.ty
      (core_includes.1 _ _ function_registered)
      ((TypeFormed.function _ function_registered boolean_formed boolean_formed).mono core_includes)
      identityType_admissible.1
    predicate := identityPredicate
    witness := DefinitionAdapters.Controls.identityTerm
    output := makeTypeOperatorDefinition identityTypeRequest identityPredicate
      DefinitionAdapters.Controls.identityTerm identityType_application rfl }

theorem defined_core_admitted :
    admitTypeInTheory coreContext certificates identityTypeRequest = some definedCore := by
  rw [admitTypeInTheory_eq_fromApplication _ _ _ _ _ identityType_application]
  have inputs : annotationsFormedB coreContext.signature certificates identityPredicate.term = true ∧
      annotationsFormedB coreContext.signature certificates
        DefinitionAdapters.Controls.identityTerm.term = true := by
    simp [annotationsFormedB, identityPredicate, DefinitionAdapters.Controls.identityTerm,
      CanonicalTerm.applicationOfFunction, CanonicalTerm.constant, typeFormedB,
      constantInstanceB, coreContext, baseContext, booleanContext, TheoryContext.addConstant,
      TheoryContext.addTypeOperator, TheoryContext.empty, Signature.addConstant,
      Signature.addTypeOperator, certificates, equalityParameter,
      Const.equality, TypeOp.bool, TypeOp.function, Ty.equality, Ty.function, Ty.bool,
      Const.same, TypeOp.same, TypeSubst.lookup, Ty.destFunction?, Name.global]
  have represented : typeFormedB coreContext.signature DefinitionAdapters.Controls.identityTerm.ty = true :=
    (typeFormedB_eq_true_iff _ _).mpr
      ((TypeFormed.function _ function_registered boolean_formed boolean_formed).mono core_includes)
  have sourceChecked := checkTypeOperatorDefinition_eq_make identityTypeRequest identityPredicate
    DefinitionAdapters.Controls.identityTerm identityType_application rfl
    identityPredicateSource_checked rfl (.app .const (.abs .bound))
    List.nodup_nil ?_
  · have names : TypeNamesFresh coreContext.names identityTypeRequest ∧
        identityTypeRequest.typeVariables = sortedParameters identityTypeRequest.predicateSource :=
      ⟨identityType_admissible.1, identityType_admissible.2.2⟩
    simp only [admitTypeInTheoryFromApplication, if_pos inputs, dif_pos represented,
      dif_pos (core_includes.1 _ _ function_registered), dif_pos identityType_admissible.1,
      admitType, if_pos names, sourceChecked]
    rfl
  · simp [identityTypeRequest, identityPredicate, DefinitionAdapters.Controls.identityTerm,
      CanonicalTerm.applicationOfFunction, CanonicalTerm.constant, DBTerm.typeVariables,
      Ty.equality, Ty.function, Ty.bool, Ty.typeVariables, Ty.typeVariablesList]

def definedType : SourceTypeDefinitionResult :=
  ⟨definedCore, makePointwiseTypeOperatorDefinition identityTypeRequest identityPredicate
    DefinitionAdapters.Controls.identityTerm identityType_application rfl⟩

theorem defined_type_admitted :
    admitSourceTypeInTheory coreContext certificates identityTypeRequest = some definedType := by
  unfold admitSourceTypeInTheory
  rw [CanonicalTerm.applicationView?_eq_some _ _ _ identityType_application]
  have core : admitTypeInTheoryFromApplication coreContext certificates identityTypeRequest
      identityPredicate DefinitionAdapters.Controls.identityTerm identityType_application = some definedCore := by
    rw [← admitTypeInTheory_eq_fromApplication _ _ _ _ _ identityType_application]
    exact defined_core_admitted
  simp only [core]
  rw [dif_pos ((CanonicalTerm.isBoolB_eq_true_iff _).mpr (by rfl))]
  rfl

theorem defined_type_formation :
    theoremFormedB definedType.context.signature certificates
        definedType.output.abstractionRepresentationTheorem = true ∧
      theoremFormedB definedType.context.signature certificates
        definedType.output.representationAbstractionTheorem = true := by
  simp [definedType, definedCore, theoremFormedB, sequentFormedB, makeTypeOperatorDefinition, makePointwiseTypeOperatorDefinition, makeTypeOperatorDefinitionWithPresentation,
    identityTypeRequest, identityExistence, Theorem.emptyResult,
    CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB,
    CanonicalTerm.applicationOfFunction, CanonicalTerm.constant, CanonicalTerm.free,
    CanonicalTerm.abstractFree, identityPredicate, DefinitionAdapters.Controls.identityTerm,
    DBTerm.closeFreeAt, annotationsFormedB, typeFormedB, constantInstanceB,
    coreContext, baseContext, booleanContext, TheoryContext.typeDefinitionExtension,
    TheoryContext.addConstant, TheoryContext.addTypeOperator, TheoryContext.empty,
    Signature.addConstant, Signature.addTypeOperator, certificates, equalityParameter,
    Const.equality, TypeOp.bool, TypeOp.function, Ty.equality, Ty.function, Ty.bool,
    Const.same, TypeOp.same, ConstProvenance.same, TypeOpProvenance.same,
    Ty.same, TypeSubst.lookup, Ty.destFunction?, Name.global]

def withDefinedType : State :=
  ⟨definedType.context,
    #[identityExistence, definedType.output.abstractionRepresentationTheorem,
      definedType.output.representationAbstractionTheorem],
    #[⟨existenceCommand, [identityExistence]⟩,
      ⟨typeCommand, [definedType.output.abstractionRepresentationTheorem,
        definedType.output.representationAbstractionTheorem]⟩]⟩

theorem type_definition_applied :
    apply emptyAxiomPolicy withExistence typeCommand = some withDefinedType := by
  simp only [apply, Command.check, withExistence, typeCommand]
  change ((if identityExistence.structuralSame identityTypeRequest.existence then
      (admitSourceTypeInTheory coreContext certificates identityTypeRequest).bind (fun defined =>
        if theoremFormedB defined.context.signature certificates
            defined.output.abstractionRepresentationTheorem = true ∧
            theoremFormedB defined.context.signature certificates
              defined.output.representationAbstractionTheorem = true then
          some (⟨defined.context, [defined.output.abstractionRepresentationTheorem,
            defined.output.representationAbstractionTheorem]⟩ : Output)
        else none)
    else none).bind (fun result => some
      (⟨result.context, #[identityExistence] ++ result.theorems.toArray,
        #[⟨existenceCommand, [identityExistence]⟩].push
          ⟨typeCommand, result.theorems⟩⟩ : State))) = some withDefinedType
  have same : identityExistence.structuralSame identityTypeRequest.existence = true :=
    (Theorem.structuralSame_eq_true_iff _ _).mpr rfl
  rw [if_pos same, defined_type_admitted]
  simp only [defined_type_formation.1, defined_type_formation.2, and_self, if_true,
    Option.bind_some]
  rfl

theorem type_definition_checked :
    (apply emptyAxiomPolicy withExistence typeCommand).isSome = true := by
  rw [type_definition_applied]
  rfl

theorem definition_history_replayed :
    replayFrom emptyAxiomPolicy (empty coreContext) [existenceCommand, typeCommand] =
      some withDefinedType := by
  simp [replayFrom, existence_applied, type_definition_applied]

theorem definition_history_reachable :
    (gslt emptyAxiomPolicy).MultiStep (empty coreContext) withDefinedType :=
  replayFrom_reachable _ _ _ _ definition_history_replayed

theorem withDefinedType_valid : Valid emptyAxiomPolicy withDefinedType := by
  apply apply_preserves_derivations emptyAxiomPolicy withExistence_valid
  exact type_definition_applied

/-- A hypothesis-free theorem record does not supply its own proof. -/
theorem unproved_existence_refused :
    apply emptyAxiomPolicy (empty coreContext) typeCommand = none := rfl

theorem type_definition_retains_existence_address :
    withDefinedType.cache[0]? = some identityExistence := by
  apply apply_preserves_lookup emptyAxiomPolicy
    (before := withExistence) (command := typeCommand)
  · exact type_definition_applied
  · rfl

theorem type_definition_has_two_outputs :
    withDefinedType.cache.size = 3 ∧ withDefinedType.receipts.size = 2 := by
  exact ⟨rfl, rfl⟩

theorem type_definition_retains_parent :
    (withDefinedType.receipts[1]'(by rw [type_definition_has_two_outputs.2]; decide)).command.parents = [0] := rfl

def falseExistence : Theorem :=
  Theorem.emptyResult ∅ Mettapedia.Languages.OpenTheory.falsity

def wrongExistenceCommand : Command :=
  .typeDefinition ("wrong-existence", 1)
    { identityTypeRequest with existence := falseExistence } 0 certificates

/-- A previously checked but different theorem cannot fill the required
existence premise merely by occupying the requested cache address. -/
theorem wrong_existence_refused :
    apply emptyAxiomPolicy withExistence wrongExistenceCommand = none := by
  have different : identityExistence ≠ falseExistence := by
    intro equal
    have terms := congrArg (fun fact : Theorem => fact.sequent.concl.term) equal
    change CanonicalTerm.equalityDB DefinitionAdapters.Controls.identityTerm.ty
      DefinitionAdapters.Controls.identityTerm.term DefinitionAdapters.Controls.identityTerm.term =
      PrimitiveSentences.falsityDB at terms
    simp [CanonicalTerm.equalityDB, DefinitionAdapters.Controls.identityTerm,
      PrimitiveSentences.falsityDB, PrimitiveSentences.truthDB, PrimitiveSentences.identityBool] at terms
  simp [apply, Command.check, withExistence, wrongExistenceCommand, different]

def undeclaredTerm : CanonicalTerm :=
  CanonicalTerm.constant (.mk (Name.global "notDeclared") .undefined) Ty.bool

def undeclaredReflexivity : Theorem :=
  Theorem.emptyResult ∅ (CanonicalTerm.equalityOfSameType undeclaredTerm undeclaredTerm rfl)

def undeclaredCommand : Command :=
  .proof ⟨undeclaredReflexivity, .inference (.refl undeclaredTerm), [], ("undeclared", 0)⟩ certificates

/-- Raw reflexivity still obeys declaration ingress in the selected theory. -/
theorem undeclared_constant_refused :
    apply emptyAxiomPolicy (empty coreContext) undeclaredCommand = none := by
  have formation : requestFormedB coreContext.signature certificates
      (.inference (.refl undeclaredTerm)) = false := by
    simp [requestFormedB, InferenceFormation.check, InferenceFormation.types,
      InferenceFormation.terms, undeclaredTerm, CanonicalTerm.constant,
      annotationsFormedB, constantInstanceB, coreContext, baseContext, booleanContext,
      TheoryContext.addConstant, TheoryContext.addTypeOperator, TheoryContext.empty,
      Signature.addConstant, Const.same, Const.equality, Name.global]
    simp [typeFormedB, Signature.addTypeOperator, Ty.bool, TypeOp.bool, TypeOp.function,
      TypeOp.same, Name.global]
  simp only [apply, empty, undeclaredCommand, Command.check]
  cases replayed : DerivationGraph.Node.replay (ruleWitness emptyAxiomPolicy) #[]
      (⟨undeclaredReflexivity, .inference (.refl undeclaredTerm), [], ("undeclared", 0)⟩ : Receipt)
  · rfl
  · simp [formation]

end Controls

def Command.requestedAxiom : Command → Option Sequent
  | .proof node _ => node.witness.requestedAxiom
  | .constant _ _ _ _ | .typeDefinition _ _ _ _ => none

theorem Command.check_policy_congr (first second : AxiomPolicy) [DecidablePred first] [DecidablePred second]
    (command : Command) (context : DefinitionAdapters.TheoryContext) (cache : Array Theorem)
    (agree : ∀ sequent, command.requestedAxiom = some sequent → (first sequent ↔ second sequent)) :
    command.check first context cache = command.check second context cache := by
  cases command with
  | proof node witnesses =>
    simp only [Command.check,ProofExecution.replay_policy_congr first second node cache agree]
  | constant => rfl
  | typeDefinition => rfl

theorem apply_policy_congr (first second : AxiomPolicy) [DecidablePred first] [DecidablePred second]
    (before : State) (command : Command)
    (agree : ∀ sequent, command.requestedAxiom = some sequent → (first sequent ↔ second sequent)) :
    apply first before command = apply second before command := by
  simp only [apply,Command.check_policy_congr first second command before.context before.cache agree]

theorem replayFrom_policy_congr (first second : AxiomPolicy) [DecidablePred first] [DecidablePred second]
    (before : State) (commands : List Command)
    (agree : ∀ command ∈ commands, ∀ sequent,
      command.requestedAxiom = some sequent → (first sequent ↔ second sequent)) :
    replayFrom first before commands = replayFrom second before commands := by
  induction commands generalizing before with
  | nil => rfl
  | cons head tail ih =>
    simp only [replayFrom,apply_policy_congr first second before head (agree head List.mem_cons_self)]
    cases applied : apply second before head with
    | none => rfl
    | some middle =>
      exact ih middle (fun command member => agree command (List.mem_cons_of_mem _ member))

theorem requested_axiom_formed {selected : AxiomPolicy} [DecidablePred selected]
    {context : TheoryContext} {cache : Array Theorem} {command : Command} {output : Output} {sequent : Sequent}
    (requested : command.requestedAxiom = some sequent)
    (accepted : command.check selected context cache = some output) :
    selected sequent ∧ AnnotationsFormed context.signature sequent.concl.term := by
  cases command with
  | constant => cases requested
  | typeDefinition => cases requested
  | proof node witnesses =>
    cases kind : node.witness with
    | inference => simp [Command.requestedAxiom,RuleRequest.requestedAxiom,kind] at requested
    | «axiom» actual =>
      have same : actual = sequent := Option.some.inj (by simpa [Command.requestedAxiom,RuleRequest.requestedAxiom,kind] using requested)
      subst sequent
      simp only [Command.check] at accepted
      cases replayed : node.replay (ruleWitness selected) cache with
      | none => simp [replayed] at accepted
      | some next =>
        rw [replayed] at accepted
        change (if requestFormedB context.signature witnesses node.witness = true ∧
            theoremFormedB context.signature witnesses node.conclusion = true then
          some (⟨context,[node.conclusion]⟩ : Output) else none) = some output at accepted
        split at accepted
        · rename_i formation
          obtain ⟨premises,found,checked,_⟩ := (node.replay_eq_some_iff (ruleWitness selected) cache next).mp replayed
          have sourceCheck : node.witness.isInstance selected premises node.conclusion = true := checked
          have semantic := (RuleRequest.isInstance_eq_true_iff selected _ _ _).mp sourceCheck |>.2
          rw [kind] at semantic
          have formed := theoremFormedB_sound context.signature witnesses formation.2
          refine ⟨semantic.2.1,(formed.2 actual ?_).1⟩
          rw [semantic.2.2.2.1]
          exact Finset.mem_singleton_self _
        · contradiction

theorem apply_check_exists {selected : AxiomPolicy} [DecidablePred selected]
    {before after : State} {command : Command}
    (accepted : apply selected before command = some after) :
    ∃ output, command.check selected before.context before.cache = some output := by
  cases checked : command.check selected before.context before.cache with
  | none => simp [apply,checked] at accepted
  | some output => exact ⟨output,rfl⟩

end Registered

end Mettapedia.Languages.HOLLight.ProofExecution
