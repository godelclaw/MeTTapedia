import Mettapedia.Languages.HOLLight.ExportCodec
import Mathlib.Logic.Function.Iterate
import Mettapedia.Coalgebra.CoherentPrefixTower

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

/-- Explicit proof work retains the last accepted receiver state even on
refusal. The refused input stays at the head of `remaining`; `consumed` counts
accepted source events, not primitive instructions or theorem outputs. -/
structure EventWork where
  retained : State
  remaining : List Json
  consumed : Nat
  rejected : Bool

def eventWork (before : State) (inputs : List Json) : EventWork :=
  ⟨before, inputs, 0, false⟩

/-- One source event is supplied to the existing receiver. A refused event
does not alter the accepted theory, receipts, address map or residual input.
Neither refused nor completed work is executed again. -/
def tickWork (policy : AxiomPolicy) [DecidablePred policy] (work : EventWork) : EventWork :=
  if work.rejected then work
  else match work.remaining with
    | [] => work
    | input :: inputs =>
        match receive? policy work.retained input with
        | none => { work with rejected := true }
        | some after => ⟨after, inputs, work.consumed + 1, false⟩

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

/-- Exhausted budget is pending work; only an empty unrejected input queue
certifies completion. -/
def EventWork.Settled (work : EventWork) : Prop :=
  work.rejected = true ∨ work.remaining = []

def EventWork.Completed (work : EventWork) : Prop :=
  work.rejected = false ∧ work.remaining = []

theorem tickWork_settled (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) (settled : work.Settled) : tickWork policy work = work := by
  rcases settled with rejected | exhausted
  · simp [tickWork, rejected]
  · simp [tickWork, exhausted]

theorem advanceWork_settled (policy : AxiomPolicy) [DecidablePred policy]
    (fuel : Nat) (work : EventWork) (settled : work.Settled) :
    advanceWork policy fuel work = work := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [advanceWork_succ, tickWork_settled policy work settled, ih]

/-- The existing work runner is an inhabitant of the shared retained-state
interface. No proof search or replay is hidden in this adapter. -/
def workTrajectory (policy : AxiomPolicy) [DecidablePred policy] (work : EventWork) :
    Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory
      (advanceWork policy) work :=
  Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory.canonical
    (advanceWork policy) work (advanceWork_zero policy)
    (fun first second state => (advanceWork_add policy first second state).symm)

/-- The residual has the same full-history receiver meaning. This observer
is used for the proof; resumption executes `tickWork`, not this fold. -/
def EventWork.meaning (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) : Option State :=
  if work.rejected then none else receiveMany? policy work.retained work.remaining

theorem tickWork_meaning (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) : (tickWork policy work).meaning policy = work.meaning policy := by
  rcases work with ⟨retained, remaining, consumed, rejected⟩
  cases rejected with
  | true => rfl
  | false =>
      cases remaining with
      | nil => rfl
      | cons input rest =>
          cases checked : receive? policy retained input <;>
            simp [tickWork, EventWork.meaning, receiveMany?, checked]

theorem advanceWork_meaning (policy : AxiomPolicy) [DecidablePred policy]
    (fuel : Nat) (work : EventWork) :
    (advanceWork policy fuel work).meaning policy = work.meaning policy := by
  induction fuel generalizing work with
  | zero => rfl
  | succ fuel ih => rw [advanceWork_succ, ih, tickWork_meaning]

/-- Every finite input reaches acceptance or refusal within one attempt per
input. This counts source events, including possibly expensive local checks. -/
theorem advanceWork_finishes (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) : (advanceWork policy work.remaining.length work).Settled := by
  rcases work with ⟨retained, remaining, consumed, rejected⟩
  induction remaining generalizing retained consumed rejected with
  | nil => exact Or.inr rfl
  | cons input rest ih =>
      cases rejected with
      | true =>
          rw [advanceWork_settled policy _ _ (Or.inl rfl)]
          exact Or.inl rfl
      | false =>
          simp only [List.length_cons, advanceWork_succ]
          cases checked : receive? policy retained input with
          | none =>
              simp only [tickWork, Bool.false_eq_true, ↓reduceIte, checked]
              rw [advanceWork_settled policy _ _ (Or.inl rfl)]
              exact Or.inl rfl
          | some after =>
              simpa only [tickWork, Bool.false_eq_true, ↓reduceIte, checked] using
                ih after (consumed + 1) false

/-- Completion is equivalent to acceptance by the original receiver, with
the same complete receiver state. Budget exhaustion alone proves neither. -/
theorem completed_iff_received (policy : AxiomPolicy) [DecidablePred policy]
    (before after : State) (inputs : List Json) :
    (∃ fuel, let work := advanceWork policy fuel (eventWork before inputs)
      work.Completed ∧ work.retained = after) ↔
      receiveMany? policy before inputs = some after := by
  constructor
  · rintro ⟨fuel, ⟨accepted, empty⟩, same⟩
    have meaning := advanceWork_meaning policy fuel (eventWork before inputs)
    calc
      receiveMany? policy before inputs =
          (advanceWork policy fuel (eventWork before inputs)).meaning policy := meaning.symm
      _ = some after := by simp only [EventWork.meaning, accepted, Bool.false_eq_true,
        ↓reduceIte, empty, receiveMany?, same]
  · intro received
    let work := advanceWork policy inputs.length (eventWork before inputs)
    have settled : work.Settled := advanceWork_finishes policy (eventWork before inputs)
    have meaning : work.meaning policy = some after :=
      (advanceWork_meaning policy inputs.length (eventWork before inputs)).trans received
    have notRejected : work.rejected = false := by
      cases rejected : work.rejected with
      | false => rfl
      | true => simp [EventWork.meaning, rejected] at meaning
    have empty : work.remaining = [] := by
      rcases settled with rejected | empty
      · simp [notRejected] at rejected
      · exact empty
    refine ⟨inputs.length, ⟨notRejected, empty⟩, ?_⟩
    exact Option.some.inj (by simpa [EventWork.meaning, notRejected, empty, receiveMany?] using meaning)

/-- Refusal is also reflected, rather than inferred from an empty result
cache. A finished rejected prefix cannot be repaired by later input. -/
theorem rejected_iff_received_none (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (inputs : List Json) :
    (∃ fuel, (advanceWork policy fuel (eventWork before inputs)).rejected = true) ↔
      receiveMany? policy before inputs = none := by
  constructor
  · rintro ⟨fuel, rejected⟩
    have meaning := advanceWork_meaning policy fuel (eventWork before inputs)
    calc
      receiveMany? policy before inputs =
          (advanceWork policy fuel (eventWork before inputs)).meaning policy := meaning.symm
      _ = none := by simp only [EventWork.meaning, rejected, ↓reduceIte]
  · intro refused
    let work := advanceWork policy inputs.length (eventWork before inputs)
    have settled : work.Settled := advanceWork_finishes policy (eventWork before inputs)
    have meaning : work.meaning policy = none :=
      (advanceWork_meaning policy inputs.length (eventWork before inputs)).trans refused
    refine ⟨inputs.length, ?_⟩
    cases rejected : work.rejected with
    | true => rfl
    | false =>
        have empty : work.remaining = [] := by
          rcases settled with bad | empty
          · simp [rejected] at bad
          · exact empty
        simp [EventWork.meaning, rejected, empty, receiveMany?] at meaning

theorem tickWork_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) (valid : ExportReplay.Valid policy work.retained.received) :
    ExportReplay.Valid policy (tickWork policy work).retained.received := by
  unfold tickWork
  split
  · exact valid
  · cases work.remaining with
    | nil => exact valid
    | cons input rest =>
        cases checked : receive? policy work.retained input with
        | none => simpa only [checked] using valid
        | some after =>
            simpa only [checked] using receive?_preserves_derivations policy valid checked

/-- All retained states, including those at refusal, keep source derivations
for every admitted theorem. -/
theorem advanceWork_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) (fuel : Nat)
    (valid : ExportReplay.Valid policy work.retained.received) :
    ExportReplay.Valid policy (advanceWork policy fuel work).retained.received := by
  induction fuel generalizing work with
  | zero => exact valid
  | succ fuel ih =>
      rw [advanceWork_succ]
      exact ih _ (tickWork_preserves_derivations policy work valid)

/-- The retained receiver has processed precisely an accepted prefix. The
queue and count account for each original occurrence, including equal inputs.
On refusal the unsuccessful input is still in the queue. -/
theorem advanceWork_description (policy : AxiomPolicy) [DecidablePred policy]
    (fuel : Nat) (work : EventWork) :
    ∃ acceptedInputs : List Json,
      receiveMany? policy work.retained acceptedInputs =
        some (advanceWork policy fuel work).retained ∧
      acceptedInputs ++ (advanceWork policy fuel work).remaining = work.remaining ∧
      (advanceWork policy fuel work).consumed = work.consumed + acceptedInputs.length ∧
      acceptedInputs.length ≤ fuel := by
  induction fuel generalizing work with
  | zero => exact ⟨[], rfl, rfl, (Nat.add_zero _).symm, Nat.le_refl _⟩
  | succ fuel ih =>
      by_cases rejected : work.rejected = true
      · rw [advanceWork_settled policy _ work (Or.inl rejected)]
        exact ⟨[], rfl, rfl, (Nat.add_zero _).symm, Nat.zero_le _⟩
      · have openWork : work.rejected = false := by simpa using rejected
        cases remaining : work.remaining with
        | nil =>
            rw [advanceWork_settled policy _ work (Or.inr remaining)]
            exact ⟨[], rfl, remaining, (Nat.add_zero _).symm, Nat.zero_le _⟩
        | cons input rest =>
            rw [advanceWork_succ]
            cases checked : receive? policy work.retained input with
            | none =>
                simp only [tickWork, openWork, Bool.false_eq_true, ↓reduceIte, remaining, checked]
                rw [advanceWork_settled policy _ _ (Or.inl rfl)]
                exact ⟨[], rfl, rfl, (Nat.add_zero _).symm, Nat.zero_le _⟩
            | some after =>
                simp only [tickWork, openWork, Bool.false_eq_true, ↓reduceIte, remaining, checked]
                obtain ⟨acceptedInputs, replayed, queued, count, bounded⟩ :=
                  ih (⟨after, rest, work.consumed + 1, false⟩ : EventWork)
                refine ⟨input :: acceptedInputs, ?_, ?_, ?_, ?_⟩
                · simpa [receiveMany?, checked] using replayed
                · simp only [List.cons_append, queued]
                · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using count
                · simpa only [List.length_cons] using Nat.succ_le_succ bounded

/-- Refusal records a real rejected input at the retained world. -/
theorem advanceWork_remaining (policy : AxiomPolicy) [DecidablePred policy]
    (fuel : Nat) (work : EventWork) :
    (advanceWork policy fuel work).remaining =
      work.remaining.drop ((advanceWork policy fuel work).consumed - work.consumed) := by
  obtain ⟨acceptedInputs, _, queued, count, _⟩ := advanceWork_description policy fuel work
  rw [count, Nat.add_sub_cancel_left, ← queued]
  simp

/-- Refusal records a real rejected input at the retained world. -/
def EventWork.RefusalValid (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) : Prop :=
  work.rejected = true → ∃ input rest,
    work.remaining = input :: rest ∧ receive? policy work.retained input = none

theorem tickWork_refusalValid (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) (valid : work.RefusalValid policy) :
    (tickWork policy work).RefusalValid policy := by
  by_cases rejected : work.rejected = true
  · simpa [tickWork, rejected] using valid
  · have openWork : work.rejected = false := by simpa using rejected
    cases remaining : work.remaining with
    | nil => simpa [tickWork, openWork, remaining] using valid
    | cons input rest =>
        cases checked : receive? policy work.retained input with
        | none =>
            simp only [tickWork, openWork, Bool.false_eq_true, ↓reduceIte, remaining, checked]
            exact fun _ => ⟨input, rest, rfl, checked⟩
        | some after =>
            simp [tickWork, openWork, remaining, checked, EventWork.RefusalValid]

theorem advanceWork_refusalValid (policy : AxiomPolicy) [DecidablePred policy]
    (fuel : Nat) (work : EventWork) (valid : work.RefusalValid policy) :
    (advanceWork policy fuel work).RefusalValid policy := by
  induction fuel generalizing work with
  | zero => exact valid
  | succ fuel ih =>
      rw [advanceWork_succ]
      exact ih _ (tickWork_refusalValid policy work valid)

/-- Batch acceptance keeps exactly one source receipt per accepted JSON
event. The resulting events are the actual registered source execution. -/
theorem receiveMany_receipts (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (inputs : List Json) (after : State)
    (accepted : receiveMany? policy before inputs = some after) :
    ∃ events : List ExportReplay.Event,
      after.received.receipts.toList = before.received.receipts.toList ++ events ∧
      events.length = inputs.length ∧
      ExportReplay.replayFrom policy before.received events = some after.received := by
  induction inputs generalizing before with
  | nil =>
      cases Option.some.inj accepted
      exact ⟨[], (List.append_nil _).symm, rfl, rfl⟩
  | cons input inputs ih =>
      cases checked : receive? policy before input with
      | none => simp [receiveMany?, checked] at accepted
      | some middle =>
          have later : receiveMany? policy middle inputs = some after := by
            simpa [receiveMany?, checked] using accepted
          obtain ⟨event, applied⟩ := receive?_checked policy checked
          have receipt := (ExportReplay.apply_checked policy applied).2.2.2.1
          obtain ⟨events, receipts, count, replayed⟩ := ih middle later
          refine ⟨event :: events, ?_, by simp [count], ?_⟩
          · rw [receipts, receipt]
            simp [List.append_assoc]
          · simpa [ExportReplay.replayFrom, applied] using replayed

/-- Pausing or refusing never erases an accepted receipt. The same law
applies from any retained checkpoint, rather than rebuilding the prefix. -/
theorem advanceWork_receipts_prefix (policy : AxiomPolicy) [DecidablePred policy]
    (fuel : Nat) (work : EventWork) :
    work.retained.received.receipts.toList.IsPrefix
      (advanceWork policy fuel work).retained.received.receipts.toList := by
  obtain ⟨acceptedInputs, accepted, _⟩ := advanceWork_description policy fuel work
  obtain ⟨events, receipts, _⟩ := receiveMany_receipts policy work.retained acceptedInputs _ accepted
  exact ⟨events, receipts.symm⟩

/-- The shared trajectory's receipt observer retains provenance and
multiplicity without imposing an order on unrelated MeTTa answers. -/
theorem workTrajectory_receipts_prefix (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) (first extra : Nat) :
    ((workTrajectory policy work).observation first).retained.received.receipts.toList.IsPrefix
      ((workTrajectory policy work).observation (first + extra)).retained.received.receipts.toList :=
  (workTrajectory policy work).observer_prefix_after_resume
    (fun state => state.retained.received.receipts.toList)
    (advanceWork_receipts_prefix policy) first extra

/-- A root found in a paused or refused execution still has its original
registered derivation and displayed claim. -/
theorem retained_root_derivation (policy : AxiomPolicy) [DecidablePred policy]
    (work : EventWork) (fuel : Nat)
    (valid : ExportReplay.Valid policy work.retained.received)
    {id : Nat} {claim : Sequent} {out : Theorem}
    (found : ExportReplay.root? (advanceWork policy fuel work).retained.received id claim = some out) :
    DefinitionAdapters.TheoryDerives policy
      (advanceWork policy fuel work).retained.received.registered.context out ∧
      out.sequent = claim :=
  ExportReplay.root_derivation policy (advanceWork_preserves_derivations policy work fuel valid) found

/-- Copying a record's current theorem support cannot erase a different
remaining input queue while claiming equality of resumable work. -/
theorem distinct_queues_distinct_work (received : State)
    (first second : List Json) (consumed : Nat) (different : first ≠ second) :
    (⟨received, first, consumed, false⟩ : EventWork) ≠
      ⟨received, second, consumed, false⟩ := by
  intro equal
  exact different (congrArg EventWork.remaining equal)

namespace Controls

open DefinitionAdapters.ContextControls

/-- A receiver with the independently admitted Boolean/equality signature. -/
def initial : State :=
  { received := ExportReplay.empty coreContext
    symbols := ⟨[("fun", TypeOp.function), ("bool", TypeOp.bool)], [("=", Const.equality)]⟩ }

private def boolSyntax : Json := .arr #[.str "op", .str "bool", .arr #[]]
private def functionSyntax (a b : Json) : Json := .arr #[.str "op", .str "fun", .arr #[a, b]]
private def propositionSyntax : Json := .arr #[.str "var", .str "p", boolSyntax]
private def equalitySyntax : Json := .arr #[.str "const", .str "=",
  functionSyntax boolSyntax (functionSyntax boolSyntax boolSyntax)]
private def applicationSyntax (a b : Json) : Json := .arr #[.str "app", a, b]

/-- Two different identifiers may publish the same reflexive equality. -/
def reflexivityInput (id : Nat) : Json := Json.mkObj [
  ("id", toJson id), ("rule", .str "REFL"), ("arguments", .arr #[propositionSyntax]),
  ("theorem", Json.mkObj [("hypotheses", .arr #[]),
    ("conclusion", applicationSyntax (applicationSyntax equalitySyntax propositionSyntax)
      propositionSyntax)])]

def started : EventWork := eventWork initial [reflexivityInput 0, reflexivityInput 1]

theorem zero_budget_is_pending :
    ¬ (advanceWork emptyAxiomPolicy 0 started).Settled := by
  change ¬ (false = true ∨ [reflexivityInput 0, reflexivityInput 1] = [])
  simp

theorem pause_keeps_one_receipt :
    (advanceWork emptyAxiomPolicy 1 started).consumed = 1 ∧
    (advanceWork emptyAxiomPolicy 1 started).retained.received.receipts.size = 1 ∧
    (advanceWork emptyAxiomPolicy 1 started).remaining = [reflexivityInput 1] := by
  have count : (advanceWork emptyAxiomPolicy 1 started).consumed = 1 := by decide +kernel
  refine ⟨count, by decide +kernel, ?_⟩
  rw [advanceWork_remaining, count]
  rfl

theorem two_equal_conclusions_two_occurrences :
    (advanceWork emptyAxiomPolicy 2 started).retained.received.receipts.size = 2 ∧
    (advanceWork emptyAxiomPolicy 2 started).retained.received.registered.cache.size = 2 ∧
    ((advanceWork emptyAxiomPolicy 2 started).retained.received.receipts.toList.map
      (fun event => event.command.origin)) = [("hol-light-export", 0), ("hol-light-export", 1)] :=
  by decide +kernel

theorem complete_after_two : (advanceWork emptyAxiomPolicy 2 started).Completed := by
  have count : (advanceWork emptyAxiomPolicy 2 started).consumed = 2 := by decide +kernel
  refine ⟨by decide +kernel, ?_⟩
  rw [advanceWork_remaining, count]
  rfl

theorem resume_keeps_complete_state :
    advanceWork emptyAxiomPolicy 1 (advanceWork emptyAxiomPolicy 1 started) =
      advanceWork emptyAxiomPolicy 2 started := advanceWork_add _ _ _ _

theorem more_budget_does_not_replay (extra : Nat) :
    advanceWork emptyAxiomPolicy extra (advanceWork emptyAxiomPolicy 2 started) =
      advanceWork emptyAxiomPolicy 2 started :=
  advanceWork_settled _ _ _ (Or.inr complete_after_two.2)

def withMalformed : EventWork :=
  eventWork initial [reflexivityInput 0, .null, reflexivityInput 1]

theorem malformed_input_preserves_accepted_prefix :
    (advanceWork emptyAxiomPolicy 3 withMalformed).rejected = true ∧
    (advanceWork emptyAxiomPolicy 3 withMalformed).consumed = 1 ∧
    (advanceWork emptyAxiomPolicy 3 withMalformed).retained.received.receipts.size = 1 ∧
    (advanceWork emptyAxiomPolicy 3 withMalformed).remaining = [.null, reflexivityInput 1] := by
  have count : (advanceWork emptyAxiomPolicy 3 withMalformed).consumed = 1 := by decide +kernel
  refine ⟨by decide +kernel, count, by decide +kernel, ?_⟩
  rw [advanceWork_remaining, count]
  rfl

theorem malformed_input_cannot_be_skipped (extra : Nat) :
    advanceWork emptyAxiomPolicy extra (advanceWork emptyAxiomPolicy 3 withMalformed) =
      advanceWork emptyAxiomPolicy 3 withMalformed :=
  advanceWork_settled _ _ _ (Or.inl malformed_input_preserves_accepted_prefix.1)

theorem duplicate_identifier_refused :
    let result := advanceWork emptyAxiomPolicy 2
      (eventWork initial [reflexivityInput 0, reflexivityInput 0])
    result.rejected = true ∧ result.consumed = 1 ∧
      result.retained.received.receipts.size = 1 := by decide +kernel

/-- A displayed claim is checked against the inference output. -/
def wrongClaim : Json := Json.mkObj [
  ("id", toJson (0 : Nat)), ("rule", .str "REFL"),
  ("arguments", .arr #[propositionSyntax]),
  ("theorem", Json.mkObj [("hypotheses", .arr #[]), ("conclusion", propositionSyntax)])]

theorem wrong_claim_refused :
    (advanceWork emptyAxiomPolicy 1 (eventWork initial [wrongClaim])).rejected = true ∧
    (advanceWork emptyAxiomPolicy 1 (eventWork initial [wrongClaim])).consumed = 0 :=
  by decide +kernel

theorem retained_prefix_is_valid :
    ExportReplay.Valid emptyAxiomPolicy
      (advanceWork emptyAxiomPolicy 3 withMalformed).retained.received :=
  advanceWork_preserves_derivations _ _ _ (ExportReplay.empty_valid _ _)

end Controls

end Mettapedia.Languages.HOLLight.ExportCodec
