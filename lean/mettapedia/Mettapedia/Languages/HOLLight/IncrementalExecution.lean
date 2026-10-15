import Mettapedia.Languages.HOLLight.ExportCodec
import Mathlib.Logic.Function.Iterate

/-!
# Incremental replay of the registered HOL source calculus

The receiver already decodes each event against its current signatures,
definition identities, proof addresses and origins. Splitting an input history
preserves its complete state; it is not merely an agreement of theorem support.
Rejected histories remain rejected. Resumption uses the same axiom policy.

These laws concern the existing registered source receiver. They do not assert
the missing whole-program correspondence of the authored MeTTa checker, or
verification of a native state-cell implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ExportCodec

open Mettapedia.Languages.OpenTheory Lean

theorem receiveMany_append (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (first second : List Json) :
    receiveMany? policy before (first ++ second) =
      (receiveMany? policy before first).bind
        (fun middle => receiveMany? policy middle second) := by
  induction first generalizing before with
  | nil => rfl
  | cons input rest ih =>
      cases received : receive? policy before input with
      | none => simp [receiveMany?, received]
      | some middle => simp [receiveMany?, received, ih]

/-- A retained source-receiver result can be continued without redecoding its
prefix. The complete theory/proof state is retained by `State` itself. -/
def continueReceived (policy : AxiomPolicy) [DecidablePred policy]
    (before : Option State) (inputs : List Json) : Option State :=
  before.bind (fun state => receiveMany? policy state inputs)

theorem continue_after_prefix (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (first second : List Json) :
    continueReceived policy (receiveMany? policy before first) second =
      receiveMany? policy before (first ++ second) :=
  (receiveMany_append policy before first second).symm

theorem continue_associates (policy : AxiomPolicy) [DecidablePred policy]
    (before : Option State) (first second : List Json) :
    continueReceived policy (continueReceived policy before first) second =
      continueReceived policy before (first ++ second) := by
  cases before with
  | none => rfl
  | some state => exact continue_after_prefix policy state first second

@[simp] theorem refused_stays_refused (policy : AxiomPolicy) [DecidablePred policy]
    (inputs : List Json) : continueReceived policy none inputs = none := rfl

/-- Continuation still earns the existing proof-graph validity theorem; it
does not install an assumed soundness field in a new runtime interface. -/
theorem continued_derivations (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (first second : List Json) (after : State)
    (valid : ExportReplay.Valid policy before.received)
    (accepted : continueReceived policy (receiveMany? policy before first) second =
      some after) : ExportReplay.Valid policy after.received := by
  rw [continue_after_prefix] at accepted
  exact receiveMany?_preserves_derivations policy before (first ++ second) after valid accepted

/-- Every original event contributes to the actual registered execution.
Batch boundaries neither remove nor duplicate event occurrences. -/
theorem continued_event_history (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (first second : List Json) (after : State)
    (accepted : continueReceived policy (receiveMany? policy before first) second =
      some after) :
    ∃ events : List ExportReplay.Event,
      events.length = first.length + second.length ∧
      ExportReplay.replayFrom policy before.received events = some after.received := by
  rw [continue_after_prefix] at accepted
  obtain ⟨events, count, replayed⟩ :=
    receiveMany?_to_replay policy before (first ++ second) after accepted
  exact ⟨events, by simpa only [List.length_append] using count, replayed⟩

/-- Explicit proof work retains the whole receiver state and the input queue.
`consumed` counts attempted source events, including attempts after refusal.
It is neither a machine-instruction count nor the number of admitted proofs. -/
structure EventWork where
  received : Option State
  remaining : List Json
  consumed : Nat

def eventWork (before : State) (inputs : List Json) : EventWork :=
  ⟨some before, inputs, 0⟩

/-- One source event is supplied to the existing receiver. Empty work is
terminal. Refusal is sticky while unconsumed input remains available. -/
def tickWork (policy : AxiomPolicy) [DecidablePred policy] (work : EventWork) : EventWork :=
  match work.remaining with
  | [] => work
  | input :: inputs =>
      ⟨continueReceived policy work.received [input], inputs, work.consumed + 1⟩

def advanceWork (policy : AxiomPolicy) [DecidablePred policy]
    (fuel : Nat) (work : EventWork) : EventWork :=
  (tickWork policy)^[fuel] work

@[simp] theorem advanceWork_zero (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) : advanceWork policy 0 work = work := rfl

@[simp] theorem advanceWork_succ (policy : AxiomPolicy) [DecidablePred policy]
    (fuel : Nat) (work : EventWork) :
    advanceWork policy (fuel + 1) work = advanceWork policy fuel (tickWork policy work) :=
  Function.iterate_succ_apply _ _ _

/-- Budget splitting preserves the complete state, queue and attempt count.
No observer equivalence is substituted for equality of those components. -/
theorem advanceWork_add (policy : AxiomPolicy) [DecidablePred policy]
    (first second : Nat) (work : EventWork) :
    advanceWork policy second (advanceWork policy first work) =
      advanceWork policy (first + second) work := by
  induction first generalizing work with
  | zero => simp only [advanceWork_zero, Nat.zero_add]
  | succ first ih =>
      simpa only [advanceWork_succ, Nat.succ_add] using ih (tickWork policy work)

/-- The recursive event stepper consumes exactly a finite prefix of the
original input and realizes the existing registered receiver on that prefix. -/
theorem advanceWork_description (policy : AxiomPolicy) [DecidablePred policy]
    (fuel : Nat) (received : Option State) (inputs : List Json) (consumed : Nat) :
    advanceWork policy fuel ⟨received, inputs, consumed⟩ =
      ⟨continueReceived policy received (inputs.take fuel), inputs.drop fuel,
        consumed + min fuel inputs.length⟩ := by
  induction fuel generalizing received inputs consumed with
  | zero => cases received <;> simp [continueReceived, receiveMany?]
  | succ fuel ih =>
      cases inputs with
      | nil =>
          cases received <;>
            simp [tickWork, ih, continueReceived, receiveMany?]
      | cons input inputs =>
          simp [tickWork, ih, continue_associates,
            Nat.add_comm, Nat.add_left_comm]

/-- The receiver's independent validity theorem applies to an actual work
prefix; shaping an arbitrary record as `EventWork` does not supply validity. -/
theorem advanceWork_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    (before after : State) (inputs : List Json) (fuel : Nat)
    (valid : ExportReplay.Valid policy before.received)
    (accepted : (advanceWork policy fuel (eventWork before inputs)).received = some after) :
    ExportReplay.Valid policy after.received := by
  rw [eventWork, advanceWork_description] at accepted
  exact receiveMany?_preserves_derivations policy before (inputs.take fuel) after valid accepted

/-- Copying a record's current theorem support cannot erase a different
remaining input queue while claiming equality of resumable work. -/
theorem distinct_queues_distinct_work (received : Option State)
    (first second : List Json) (consumed : Nat) (different : first ≠ second) :
    (⟨received, first, consumed⟩ : EventWork) ≠ ⟨received, second, consumed⟩ := by
  intro equal
  exact different (congrArg EventWork.remaining equal)

end Mettapedia.Languages.HOLLight.ExportCodec
