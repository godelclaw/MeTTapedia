import Mettapedia.Languages.HOLLight.ProofSystem

/-!
# Policy independence of inference-only HOL Light replay

An axiom policy is consulted only by an axiom request. A retained graph whose
every physical node is an inference therefore has exactly the same replay,
including its cache and selected root, under any two policies. Merely having
an axiom-free root theorem does not supply this whole-graph condition.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.InferenceOnlyReplay
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution

def isInference (receipt : Receipt) : Bool := match receipt.witness with
  | .inference _ => true
  | .axiom _ => false

def inferenceOnly (receipts : List Receipt) : Bool := receipts.all isInference

variable (first second : AxiomPolicy) [DecidablePred first] [DecidablePred second]

theorem node_replay (receipt : Receipt) (cache : Array Theorem)
    (retained : isInference receipt = true) :
    receipt.replay (ruleWitness first) cache = receipt.replay (ruleWitness second) cache := by
  rcases receipt with ⟨conclusion, request, parents, origin⟩
  cases request with
  | inference request => rfl
  | «axiom» sequent => cases retained

theorem replay_from (receipts : List Receipt) (retained : inferenceOnly receipts = true)
    (cache : Array Theorem) :
    DerivationGraph.replayFrom (ruleWitness first) cache receipts =
      DerivationGraph.replayFrom (ruleWitness second) cache receipts := by
  induction receipts generalizing cache with
  | nil => rfl
  | cons receipt rest ih =>
    have split : isInference receipt = true ∧ inferenceOnly rest = true := by
      simpa only [inferenceOnly, List.all_cons, Bool.and_eq_true] using retained
    obtain ⟨head, tail⟩ := split
    simp only [DerivationGraph.replayFrom, node_replay first second receipt cache head]
    cases receipt.replay (ruleWitness second) cache with
    | none => rfl
    | some next => exact ih tail next

theorem checker (claim : Theorem) (certificate : ProofSystem.Certificate)
    (retained : inferenceOnly certificate.1 = true) :
    (ProofSystem.checker first).check claim certificate =
      (ProofSystem.checker second).check claim certificate := by
  simp only [ProofSystem.checker, DerivationGraph.replay,
    replay_from first second certificate.1 retained]

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

theorem node_inference_of_empty_replay {receipt : Receipt} {before after : Array Theorem}
    (accepted : receipt.replay (ruleWitness emptyAxiomPolicy) before = some after) :
    isInference receipt = true := by
  cases found : receipt.witness with
  | inference request => simp only [isInference, found]
  | «axiom» sequent =>
    obtain ⟨premises, _, valid, _⟩ :=
      (DerivationGraph.Node.replay_eq_some_iff (ruleWitness emptyAxiomPolicy) before after receipt).mp accepted
    rw [found] at valid
    have semantics := (RuleRequest.isInstance_eq_true_iff emptyAxiomPolicy _ premises receipt.conclusion).mp valid
    obtain ⟨_, forbidden, _⟩ := semantics.2
    exact forbidden.elim

theorem inference_only_of_empty_replay (receipts : List Receipt) {before after : Array Theorem}
    (accepted : DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy) before receipts = some after) :
    inferenceOnly receipts = true := by
  induction receipts generalizing before with
  | nil => rfl
  | cons receipt rest ih =>
    cases first : receipt.replay (ruleWitness emptyAxiomPolicy) before with
    | none =>
      simp only [DerivationGraph.replayFrom, first, Option.bind_eq_bind, Option.bind_none] at accepted
      cases accepted
    | some next =>
      have later : DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy) next rest = some after := by
        simpa only [DerivationGraph.replayFrom, first, Option.bind_eq_bind, Option.bind_some] using accepted
      simpa only [inferenceOnly, List.all_cons, Bool.and_eq_true] using
        And.intro (node_inference_of_empty_replay first) (ih later)

theorem inference_only_of_empty_acceptance (claim : Theorem) (certificate : ProofSystem.Certificate)
    (accepted : (ProofSystem.checker emptyAxiomPolicy).check claim certificate = true) :
    inferenceOnly certificate.1 = true := by
  obtain ⟨cache, replayed, _⟩ := (ProofSystem.checker_check_iff emptyAxiomPolicy claim certificate).mp accepted
  exact inference_only_of_empty_replay certificate.1 replayed

#print axioms node_replay
#print axioms replay_from
#print axioms checker
#print axioms inference_only_of_empty_acceptance
end Mettapedia.Languages.HOLLight.InferenceOnlyReplay
