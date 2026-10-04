import Std

/-!
# Common LLM request, completion and admission boundary

Messages, tool identities and opaque reasoning belong to the protocol. The
operator admission policy is separate and can be bypassed for upstream cores.
The model connects to `src/llm_boundary.metta`, `provider_protocol.py` and
`llm_policy.py` through their request handles and terminal observations.

The claims cover this executable model, not the correctness of C, provider
JSON decoders, cryptographic signatures or the external service. The host must
allocate distinct handles, correlate observations faithfully, serialize the
ledger transaction, and not retry HTTP inside one submitted request.
-/
namespace MeTTaClaw.LlmBoundary

inductive Role where
  | system | user | assistant | tool
  deriving DecidableEq, Repr

structure ToolCall where
  id : String
  name : String
  argumentsJson : String
  deriving DecidableEq, Repr

structure Message where
  role : Role
  text : String
  calls : List ToolCall := []
  toolResultFor : Option String := none
  opaqueReasoning : List String := []
  deriving DecidableEq, Repr

structure Request where
  correlation : Nat
  messages : List Message
  maxOutput : Nat
  effort : Option String
  deriving DecidableEq, Repr

structure Handle where
  epoch : Nat
  transport : Nat
  deriving DecidableEq, Repr

structure Usage where
  input : Nat
  output : Nat
  cached : Nat
  reasoning : Nat
  deriving DecidableEq, Repr

inductive Completion where
  | answered (message : Message) (usage : Usage)
  | truncated (partialMessage : Message) (usage : Usage)
  | failed (kind : String)
  | cancelled
  deriving DecidableEq, Repr

inductive Phase where
  | idle
  | pending (request : Request) (handle : Handle)
  | terminal (request : Request) (handle : Handle) (result : Completion)
  deriving DecidableEq, Repr

structure Observation where
  handle : Handle
  result : Completion
  deriving DecidableEq, Repr

def observe (state : Phase) (event : Observation) : Phase :=
  match state with
  | .pending request handle =>
      if event.handle = handle then .terminal request handle event.result else state
  | _ => state

def delivers (state : Phase) (event : Observation) : Bool :=
  match state with
  | .pending _ handle => decide (event.handle = handle)
  | _ => false

theorem terminal_is_stable (request : Request) (handle : Handle)
    (result : Completion) (event : Observation) :
    observe (.terminal request handle result) event = .terminal request handle result := rfl

theorem wrong_handle_is_ignored (request : Request) (handle : Handle)
    (event : Observation) (different : event.handle ≠ handle) :
    observe (.pending request handle) event = .pending request handle := by
  simp [observe, different]

theorem completion_is_idempotent (state : Phase) (event : Observation) :
    observe (observe state event) event = observe state event := by
  cases state with
  | idle => rfl
  | terminal => rfl
  | pending request handle =>
      by_cases h : event.handle = handle <;> simp [observe, h]

theorem delivered_once (state : Phase) (event : Observation)
    (accepted : delivers state event = true) :
    delivers (observe state event) event = false := by
  cases state with
  | idle => simp [delivers] at accepted
  | terminal => simp [delivers] at accepted
  | pending request handle =>
      have same : event.handle = handle := of_decide_eq_true accepted
      simp [observe, delivers, same]

inductive Profile where
  | upstream | managed
  deriving DecidableEq, Repr

structure Limits where
  -- Zero disables a cap, matching the operator configuration.
  requests : Nat
  output : Nat
  deriving DecidableEq, Repr

structure Accounting where
  requests : Nat
  reservedAndUsedOutput : Nat
  deriving DecidableEq, Repr

def admitted (profile : Profile) (limit : Limits) (used : Accounting)
    (request : Request) : Bool :=
  match profile with
  | .upstream => true
  | .managed => decide
      ((limit.requests = 0 ∨ used.requests + 1 ≤ limit.requests) ∧
       (limit.output = 0 ∨ used.reservedAndUsedOutput + request.maxOutput ≤ limit.output))

def reserve (used : Accounting) (request : Request) : Accounting :=
  { requests := used.requests + 1
    reservedAndUsedOutput := used.reservedAndUsedOutput + request.maxOutput }

theorem upstream_adds_no_budget (limit : Limits) (used : Accounting) (request : Request) :
    admitted .upstream limit used request = true := rfl

theorem managed_reservation_preserves_caps (limit : Limits) (used : Accounting)
    (request : Request) (accepted : admitted .managed limit used request = true) :
    (limit.requests = 0 ∨ (reserve used request).requests ≤ limit.requests) ∧
    (limit.output = 0 ∨ (reserve used request).reservedAndUsedOutput ≤ limit.output) := by
  simpa [admitted, reserve] using accepted

-- A lost reply is not evidence of zero billable output. Only a known terminal
-- usage observation can release part of a reservation.
def releaseUnused (reserved : Nat) (knownOutput : Option Nat) : Nat :=
  match knownOutput with
  | none => reserved
  | some output => output

theorem uncertain_request_keeps_reservation (reserved : Nat) :
    releaseUnused reserved none = reserved := rfl

theorem observed_usage_refines_reservation (reserved output : Nat)
    (hostBound : output ≤ reserved) : releaseUnused reserved (some output) ≤ reserved := by
  exact hostBound

-- The same boundary observations used by the native fixture: a foreign event,
-- a matching completion, then its duplicate. Neither foreign nor duplicate
-- completion delivers a second answer.
def fixtureRequest : Request := ⟨17, [], 42, some "low"⟩
def fixtureHandle : Handle := ⟨1, 7⟩
def fixtureForeign : Observation := ⟨⟨1, 8⟩, .failed "foreign"⟩
def fixtureCompletion : Observation := ⟨fixtureHandle, .failed "fixture"⟩

example : observe (.pending fixtureRequest fixtureHandle) fixtureForeign =
    .pending fixtureRequest fixtureHandle := by decide
example : delivers (.pending fixtureRequest fixtureHandle) fixtureCompletion = true := by decide
example : delivers (observe (.pending fixtureRequest fixtureHandle) fixtureCompletion)
    fixtureCompletion = false := by decide

#print axioms completion_is_idempotent
#print axioms delivered_once
#print axioms managed_reservation_preserves_caps

end MeTTaClaw.LlmBoundary
