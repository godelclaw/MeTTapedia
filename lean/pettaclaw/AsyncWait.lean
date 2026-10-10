import Init

/-!
# Soft waiting and owned terminal observations

An attention deadline changes only whether the caller waits. It does not
cancel transport, erase the captured request, or grant permission to retry.
Transport activity is distinct from a complete provider response. A completed
answer is retained even when its captured authority has become stale.

This small executable transport contract complements TopicAsync and
CooperativeInput. Network delivery and durable atomic journaling are host
assumptions; this model asserts neither remote exactly-once execution nor
recovery of an HTTP connection after process death.
-/
namespace AsyncWait

structure Identity where
  owner : Nat
  generation : Nat
  serial : Nat
deriving Repr, DecidableEq

inductive Terminal where
  | answer (value : Nat)
  | transportFailure
  | cancelled
  | interruptedUnknown
deriving Repr, DecidableEq

structure Call where
  id : Identity
  capturedRevision : Nat
  sent : Bool := false
  waiting : Bool := true
  bytes : Nat := 0
  terminal : Option Terminal := none
  adopted : Bool := false
deriving Repr, DecidableEq

def softWait (call : Call) : Call := { call with waiting := false }
def progress (call : Call) (bytes : Nat) : Call := { call with bytes := bytes }
def settle (call : Call) (id : Identity) (outcome : Terminal) : Call :=
  if call.id = id ∧ call.terminal = none then
    { call with terminal := some outcome, waiting := false }
  else call
def recover (call : Call) : Call :=
  if call.sent ∧ call.terminal = none then
    settle call call.id .interruptedUnknown
  else call
def adopt (call : Call) (revision : Nat) : Call :=
  match call.terminal with
  | some (.answer _) =>
      if call.capturedRevision = revision then { call with adopted := true } else call
  | _ => call
def canSubmit (call : Option Call) : Bool := call.isNone

theorem soft_preserves_identity (call : Call) : (softWait call).id = call.id := rfl
theorem soft_preserves_terminal (call : Call) : (softWait call).terminal = call.terminal := rfl
theorem soft_preserves_sent (call : Call) : (softWait call).sent = call.sent := rfl
theorem soft_preserves_authority (call : Call) :
    (softWait call).capturedRevision = call.capturedRevision := rfl
theorem soft_is_idempotent (call : Call) : softWait (softWait call) = softWait call := rfl
theorem soft_never_grants_another_submission (call : Call) :
    canSubmit (some (softWait call)) = false := rfl
theorem progress_is_not_completion (call : Call) (bytes : Nat) :
    (progress call bytes).terminal = call.terminal := rfl
theorem progress_is_not_authority (call : Call) (bytes : Nat) :
    (progress call bytes).adopted = call.adopted := rfl
theorem foreign_reply_stutters (call : Call) (id : Identity) (outcome : Terminal)
    (foreign : call.id ≠ id) : settle call id outcome = call := by simp [settle, foreign]
theorem terminal_is_immutable (call : Call) (id : Identity) (first second : Terminal)
    (done : call.terminal = some first) : settle call id second = call := by simp [settle, done]
theorem completion_after_soft_wait (call : Call) (value : Nat) (pending : call.terminal = none) :
    (settle (softWait call) call.id (.answer value)).terminal = some (.answer value) := by
  simp [settle, softWait, pending]
theorem settlement_preserves_owner (call : Call) (id : Identity) (outcome : Terminal) :
    (settle call id outcome).id = call.id := by simp only [settle]; split <;> rfl
theorem duplicate_settlement (call : Call) (id : Identity) (first second : Terminal) :
    settle (settle call id first) id second = settle call id first := by
  by_cases accepted : call.id = id ∧ call.terminal = none
  · simp [settle, accepted]
  · simp [settle, accepted]
theorem stale_answer_retained (call : Call) (value revision : Nat)
    (done : call.terminal = some (.answer value))
    (stale : call.capturedRevision ≠ revision) : adopt call revision = call := by
  simp [adopt, done, stale]
theorem adoption_requires_complete_answer (call : Call) (revision : Nat)
    (pending : call.terminal = none) : adopt call revision = call := by simp [adopt, pending]
theorem recovery_records_uncertainty (call : Call)
    (sent : call.sent = true) (pending : call.terminal = none) :
    (recover call).terminal = some .interruptedUnknown := by simp [recover, settle, sent, pending]
theorem recovered_call_cannot_act (call : Call) (revision : Nat)
    (sent : call.sent = true) (pending : call.terminal = none) :
    adopt (recover call) revision = recover call := by
  simp [adopt, recover, settle, sent, pending]
theorem settled_recovery_stutters (call : Call) (terminal : Terminal)
    (done : call.terminal = some terminal) : recover call = call := by simp [recover, done]

def fixture : Call := { id := ⟨1, 2, 3⟩, capturedRevision := 4, sent := true }
example : (settle (softWait fixture) fixture.id (.answer 5)).terminal = some (.answer 5) := by decide
example : (adopt (settle (softWait fixture) fixture.id (.answer 5)) 6).adopted = false := by decide
example : (recover fixture).terminal = some .interruptedUnknown := by decide
example : settle fixture ⟨2, 2, 3⟩ (.answer 5) = fixture := by decide

end AsyncWait
