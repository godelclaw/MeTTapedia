import Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection

/-!
# Failure-preserving tool feedback

The old missing-key search path returned the same text as a successful empty
search; other exception categories all became a blank string. No downstream
policy, however capable, can recover a distinction erased by that projection.

The repaired contract keeps a tagged failure or returned result. A returned
empty list is a completed lookup, not evidence that a document was read or that
the enclosing user task is complete. The existing effect-receipt model supplies
the independent distinction between dispatcher return and effect success.

The tags here model the interface contract. The runtime's textual/JSON codecs
and health projections require separate correspondence tests. This file does
not prove that an LLM will interpret faithful feedback correctly.

Runtime witnesses are `tests/test_websearch.py`,
`tests/test_context_failure_feedback.py` and the paired Python/native
projection cases in `tests/test_runtime_context.py` / `test_runtime_cetta.py`.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.ToolFailureFeedback

inductive FailureStage where
  | preparation | provider | tool
deriving DecidableEq, Repr

inductive FailureCode where
  | missingKey | network | authentication | invalidCall | contextBudget
deriving DecidableEq, Repr

structure Failure where
  stage : FailureStage
  code : FailureCode
deriving DecidableEq, Repr

inductive Outcome where
  | returned (rows : List Nat)
  | failed (failure : Failure)
deriving DecidableEq, Repr

def missingKey : Outcome := .failed ⟨.tool, .missingKey⟩
def emptyResult : Outcome := .returned []

/-- Faithful to the observed collision: a missing key became `[]` and was
formatted as `()`, whereas exceptions were reduced to blank output. -/
def legacyText : Outcome → String
  | .returned [] => "()"
  | .returned (_ :: _) => "results"
  | .failed ⟨_, .missingKey⟩ => "()"
  | .failed _ => ""

theorem missing_key_collides_with_empty :
    legacyText missingKey = legacyText emptyResult := rfl

theorem no_policy_can_recover_erased_failure :
    ¬ ∃ classifier : String → Bool,
      classifier (legacyText missingKey) = true ∧
        classifier (legacyText emptyResult) = false := by
  rintro ⟨classify, failureCorrect, emptyCorrect⟩
  have collision := congrArg classify missing_key_collides_with_empty
  rw [failureCorrect, emptyCorrect] at collision
  cases collision

theorem network_and_authentication_diagnostics_were_erased :
    legacyText (.failed ⟨.tool, .network⟩) =
      legacyText (.failed ⟨.tool, .authentication⟩) := rfl

inductive Feedback where
  | results (rows : List Nat)
  | error (failure : Failure)
deriving DecidableEq, Repr

def encode : Outcome → Feedback
  | .returned rows => .results rows
  | .failed failure => .error failure

def decode : Feedback → Outcome
  | .results rows => .returned rows
  | .error failure => .failed failure

theorem feedback_roundtrip (outcome : Outcome) : decode (encode outcome) = outcome := by
  cases outcome <;> rfl

theorem feedback_is_injective : Function.Injective encode := by
  intro a b h
  have := congrArg decode h
  simpa only [feedback_roundtrip] using this

theorem failure_is_never_empty_success (f : Failure) :
    encode (.failed f) ≠ encode emptyResult := by
  simp [encode, emptyResult]

theorem failure_stage_and_code_survive (f : Failure) :
    decode (encode (.failed f)) = .failed f := rfl

open EffectReceiptProjection in
def receipt : Outcome → Receipt
  | .returned _ => ⟨.returned, .success⟩
  | .failed _ => ⟨.returned, .failure⟩

theorem dispatcher_return_does_not_erase_domain_failure (f : Failure) :
    (receipt (.failed f)).disposition = .returned ∧
      (receipt (.failed f)).evidence = .failure := by
  exact ⟨rfl, rfl⟩

theorem failed_lookup_cannot_authorize_effect_completion (f : Failure) :
    ¬ EffectReceiptProjection.Completed ⟨7, some (receipt (.failed f))⟩ := by
  simp [EffectReceiptProjection.Completed, receipt]

end Mettapedia.CognitiveArchitecture.Agent.ToolFailureFeedback
