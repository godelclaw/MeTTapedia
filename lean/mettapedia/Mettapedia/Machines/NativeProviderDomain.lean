import Std

/-!
# Native provider ownership, usage and completion

This is the typed application contract, independent of SQL representation.
`Focus` is the captured projection for one call and one selected attempt. The
implementation obtains it from explicit native facts, including absent facts;
the store's scoped-transaction contract validates those reads at publication.

The MeTTa implementation is `provider_domain_cetta.metta`, over
`knowledge_store_cetta.metta`. A receipt stores the original command and answer
atomically with its fact edits. The executable trace is replayed through those
actual programs and native persistence, not through another implementation of
the model. Encoding, interpreter/C execution, complete observation capture and
filesystem durability remain separate obligations; these laws do not prove
that entire stack. In particular, a submitted-attempt fact must originate with
the trusted transport owner. None of these local transitions sends a request.
-/

namespace Mettapedia.Machines.NativeProviderDomain

inductive Counter where
  | unknown
  | known (count : Nat)
  deriving DecidableEq, Repr

def mergeCounter : Counter → Counter → Option Counter
  | .unknown, incoming => some incoming
  | old, .unknown => some old
  | .known old, .known incoming => if old = incoming then some (.known old) else none

theorem counter_idempotent (count : Counter) : mergeCounter count count = some count := by
  cases count <;> simp [mergeCounter]

theorem counter_merge_commutative (left right : Counter) :
    mergeCounter left right = mergeCounter right left := by
  cases left with
  | unknown => cases right <;> rfl
  | known a =>
    cases right with
    | unknown => rfl
    | known b =>
      by_cases same : a = b
      · subst b; rfl
      · simp [mergeCounter, same, Ne.symm same]

theorem established_count_is_preserved (old : Nat) (incoming result : Counter)
    (merged : mergeCounter (.known old) incoming = some result) : result = .known old := by
  cases incoming with
  | unknown => simpa [mergeCounter] using merged.symm
  | known next =>
    by_cases same : old = next
    · simpa [mergeCounter, same] using merged.symm
    · simp [mergeCounter, same] at merged

theorem missing_is_distinct_from_reported_zero :
    mergeCounter .unknown .unknown = some .unknown ∧
    mergeCounter .unknown (.known 0) = some (.known 0) ∧
    Counter.unknown ≠ .known 0 := by decide

structure Usage where
  input : Counter := .unknown
  output : Counter := .unknown
  cached : Counter := .unknown
  written : Counter := .unknown
  deriving DecidableEq, Repr

def mergeUsage (old incoming : Usage) : Option Usage := do
  let input ← mergeCounter old.input incoming.input
  let output ← mergeCounter old.output incoming.output
  let cached ← mergeCounter old.cached incoming.cached
  let written ← mergeCounter old.written incoming.written
  return { input, output, cached, written }

theorem usage_idempotent (usage : Usage) : mergeUsage usage usage = some usage := by
  cases usage
  simp [mergeUsage, counter_idempotent]

inductive UsageStatus where
  | accepted | conflict
  deriving DecidableEq, Repr

inductive Phase where
  | active | completed | unknown | failed
  deriving DecidableEq, Repr

structure Focus where
  registered : Bool := true
  observedAttempt : String := "attempt"
  submitted : Bool := true
  lease : Option (String × Phase) := some ("attempt", .active)
  usage : Option Usage := none
  answer : Option (String × String) := none
  deriving DecidableEq, Repr

def stageUsage (state : Focus) (incoming : Usage) : Focus × UsageStatus :=
  match state.usage with
  | none => ({ state with usage := some incoming }, .accepted)
  | some old => match mergeUsage old incoming with
    | some merged => ({ state with usage := some merged }, .accepted)
    | none => (state, .conflict)

theorem staging_preserves_authority (state : Focus) (incoming : Usage) :
    (stageUsage state incoming).1.lease = state.lease ∧
    (stageUsage state incoming).1.answer = state.answer := by
  unfold stageUsage
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

theorem staging_retains_a_usage_fact (state : Focus) (incoming : Usage) :
    (stageUsage state incoming).1.usage.isSome = true := by
  unfold stageUsage
  split
  · rfl
  · split
    · rfl
    · simp_all

theorem repeated_usage_keeps_the_same_tally (state : Focus) (usage : Usage)
    (recorded : state.usage = some usage) : stageUsage state usage = (state, .accepted) := by
  rcases state with ⟨registered, attempt, submitted, lease, old, answer⟩
  simp_all [stageUsage, usage_idempotent]

inductive Command where
  | finish (attempt reference : String) (usage : Usage) (source : String := "source")
  | recordUsage (attempt : String) (usage : Usage) (source : String := "source")
  deriving DecidableEq, Repr

def Command.attempt : Command → String
  | .finish attempt .. | .recordUsage attempt .. => attempt

inductive Refusal where
  | unregistered | unsubmitted | unobservedAttempt | completedAnswerMissing
  deriving DecidableEq, Repr

inductive Outcome where
  | completed (usage : UsageStatus)
  | alreadyCompleted (usage : UsageStatus)
  | usageRecorded (usage : UsageStatus)
  | notOwned (usage : UsageStatus)
  | answerConflict (usage : UsageStatus)
  | refused (reason : Refusal)
  deriving DecidableEq, Repr

structure Decision where
  next : Focus
  outcome : Outcome
  deriving DecidableEq, Repr

def publishAnswer (staged : Focus) (attempt reference : String) : Focus :=
  { staged with lease := some (attempt, .completed), answer := some (attempt, reference) }

def ownedCompletion (original staged : Focus) (attempt reference : String)
    (usage : UsageStatus) : Decision :=
  match staged.answer with
  | none =>
    if original.lease = some (attempt, .completed) then
      ⟨original, .refused .completedAnswerMissing⟩
    else ⟨publishAnswer staged attempt reference, .completed usage⟩
  | some (owner, previous) =>
    if owner = attempt ∧ previous = reference then
      if original.lease = some (attempt, .completed) then ⟨staged, .alreadyCompleted usage⟩
      else ⟨publishAnswer staged attempt reference, .completed usage⟩
    else ⟨staged, .answerConflict usage⟩

def eligible (state : Focus) (attempt : String) : Prop :=
  state.lease = some (attempt, .active) ∨ state.lease = some (attempt, .completed)

instance (state : Focus) (attempt : String) : Decidable (eligible state attempt) :=
  inferInstanceAs (Decidable (_ ∨ _))

def plan (state : Focus) (command : Command) : Decision :=
  if !state.registered then ⟨state, .refused .unregistered⟩
  else if command.attempt ≠ state.observedAttempt then ⟨state, .refused .unobservedAttempt⟩
  else if !state.submitted then ⟨state, .refused .unsubmitted⟩
  else match command with
    | .recordUsage _ incoming _ =>
      let staged := stageUsage state incoming
      ⟨staged.1, .usageRecorded staged.2⟩
    | .finish attempt reference incoming _ =>
      let staged := stageUsage state incoming
      if eligible state attempt then ownedCompletion state staged.1 attempt reference staged.2
      else ⟨staged.1, .notOwned staged.2⟩

theorem nonowner_cannot_change_lease_or_answer (state : Focus)
    (attempt reference source : String) (incoming : Usage)
    (notOwner : ¬eligible state attempt) :
    (plan state (.finish attempt reference incoming source)).next.lease = state.lease ∧
    (plan state (.finish attempt reference incoming source)).next.answer = state.answer := by
  unfold plan
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · simp only [notOwner, ↓reduceIte]
        exact staging_preserves_authority state incoming

theorem usage_does_not_require_current_ownership (state : Focus) (attempt source : String)
    (incoming : Usage) (registered : state.registered = true)
    (selected : attempt = state.observedAttempt) (submitted : state.submitted = true) :
    plan state (.recordUsage attempt incoming source) =
      ⟨(stageUsage state incoming).1, .usageRecorded (stageUsage state incoming).2⟩ := by
  simp [plan, registered, Command.attempt, selected, submitted]

theorem completed_decision_has_matching_evidence (original staged : Focus)
    (attempt reference : String) (usage finalUsage : UsageStatus)
    (completed : (ownedCompletion original staged attempt reference usage).outcome =
      .completed finalUsage) :
    (ownedCompletion original staged attempt reference usage).next.lease = some (attempt, .completed) ∧
    (ownedCompletion original staged attempt reference usage).next.answer = some (attempt, reference) := by
  cases answer : staged.answer with
  | none =>
    by_cases previous : original.lease = some (attempt, .completed)
    · simp [ownedCompletion, answer, previous] at completed
    · simp [ownedCompletion, answer, previous, publishAnswer]
  | some pair =>
    rcases pair with ⟨owner, previous⟩
    by_cases same : owner = attempt ∧ previous = reference
    · by_cases previous : original.lease = some (attempt, .completed)
      · simp [ownedCompletion, answer, same, previous] at completed
      · simp [ownedCompletion, answer, same, previous, publishAnswer]
    · simp [ownedCompletion, answer, same] at completed

theorem usage_conflict_does_not_erase_a_received_answer (state : Focus)
    (attempt reference : String) (usage : Usage)
    (active : state.lease = some (attempt, .active)) (noAnswer : state.answer = none) :
    (ownedCompletion state (stageUsage state usage).1 attempt reference .conflict).next.answer =
      some (attempt, reference) := by
  have unchanged := (staging_preserves_authority state usage).2
  simp [ownedCompletion, unchanged, noAnswer, active, publishAnswer]

theorem successful_plan_has_matching_evidence (state : Focus)
    (attempt reference source : String) (incoming : Usage) (finalUsage : UsageStatus)
    (completed : (plan state (.finish attempt reference incoming source)).outcome =
      .completed finalUsage) :
    (plan state (.finish attempt reference incoming source)).next.lease = some (attempt, .completed) ∧
    (plan state (.finish attempt reference incoming source)).next.answer = some (attempt, reference) := by
  cases registered : state.registered with
  | false => simp [plan, registered] at completed
  | true =>
    by_cases selected : attempt = state.observedAttempt
    · subst attempt
      cases submitted : state.submitted with
      | false => simp [plan, registered, Command.attempt, submitted] at completed
      | true =>
        by_cases owner : eligible state state.observedAttempt
        · have reduction : plan state (.finish state.observedAttempt reference incoming source) =
              ownedCompletion state (stageUsage state incoming).1 state.observedAttempt reference
                (stageUsage state incoming).2 := by
            simp [plan, registered, Command.attempt, submitted, owner]
          rw [reduction] at completed ⊢
          exact completed_decision_has_matching_evidence state (stageUsage state incoming).1
            state.observedAttempt reference (stageUsage state incoming).2 finalUsage completed
        · simp [plan, registered, Command.attempt, submitted, owner] at completed
    · simp [plan, registered, Command.attempt, selected] at completed

theorem a_completed_answer_is_not_a_new_completion (state : Focus)
    (attempt reference source : String) (incoming : Usage)
    (registered : state.registered = true) (selected : attempt = state.observedAttempt)
    (submitted : state.submitted = true) (lease : state.lease = some (attempt, .completed))
    (answer : state.answer = some (attempt, reference)) :
    (plan state (.finish attempt reference incoming source)).outcome =
      .alreadyCompleted (stageUsage state incoming).2 := by
  subst attempt
  have owner : eligible state state.observedAttempt := Or.inr lease
  have unchanged := (staging_preserves_authority state incoming).2
  simp [plan, registered, Command.attempt, submitted, owner, ownedCompletion, unchanged, answer, lease]

structure Receipt where
  command : Command
  outcome : Outcome
  deriving DecidableEq, Repr

structure Ledger where
  focus : Focus := {}
  receipts : Nat → Option Receipt := fun _ => none
  providerSubmissions : Nat := 1

inductive Reply where
  | committed (outcome : Outcome)
  | replayed (outcome : Outcome)
  | collision
  deriving DecidableEq, Repr

def firstCompletion : Reply → Bool
  | .committed (.completed _) => true
  | _ => false

theorem replay_and_already_completed_do_not_grant_first_completion (usage : UsageStatus) :
    firstCompletion (.replayed (.completed usage)) = false ∧
    firstCompletion (.committed (.alreadyCompleted usage)) = false := ⟨rfl, rfl⟩

structure Execution where
  ledger : Ledger
  reply : Reply

def execute (ledger : Ledger) (identity : Nat) (command : Command) : Execution :=
  match ledger.receipts identity with
  | some receipt =>
    if receipt.command = command then ⟨ledger, .replayed receipt.outcome⟩
    else ⟨ledger, .collision⟩
  | none =>
    let decision := plan ledger.focus command
    let receipt : Receipt := ⟨command, decision.outcome⟩
    let updated : Ledger := {
      focus := decision.next
      receipts := fun other => if other = identity then some receipt else ledger.receipts other
      providerSubmissions := ledger.providerSubmissions }
    ⟨updated, .committed decision.outcome⟩

theorem an_existing_receipt_prevents_another_state_change (ledger : Ledger)
    (identity : Nat) (command : Command) (receipt : Receipt)
    (present : ledger.receipts identity = some receipt) :
    (execute ledger identity command).ledger = ledger := by
  simp only [execute, present]
  split <;> rfl

theorem replay_returns_the_original_answer (ledger : Ledger) (identity : Nat)
    (receipt : Receipt) (present : ledger.receipts identity = some receipt) :
    (execute ledger identity receipt.command).reply = .replayed receipt.outcome := by
  simp [execute, present]

theorem local_commands_never_submit_provider_requests (ledger : Ledger)
    (identity : Nat) (command : Command) :
    (execute ledger identity command).ledger.providerSubmissions = ledger.providerSubmissions := by
  unfold execute
  split
  · split <;> rfl
  · rfl

theorem fresh_execution_installs_its_receipt (ledger : Ledger) (identity : Nat)
    (command : Command) (absent : ledger.receipts identity = none) :
    (execute ledger identity command).ledger.receipts identity =
      some ⟨command, (plan ledger.focus command).outcome⟩ := by
  simp [execute, absent]

theorem a_duplicate_command_is_replayed (ledger : Ledger) (identity : Nat)
    (command : Command) (absent : ledger.receipts identity = none) :
    (execute (execute ledger identity command).ledger identity command).reply =
      .replayed (plan ledger.focus command).outcome := by
  simp [execute, absent]

inductive Publication where
  | acknowledged | rejected | lostAckLanded | lostAckNotLanded
  deriving DecidableEq, Repr

inductive Acknowledgement where
  | committed | rejected | uncertain
  deriving DecidableEq, Repr

def acknowledgement : Publication → Acknowledgement
  | .acknowledged => .committed
  | .rejected => .rejected
  | .lostAckLanded | .lostAckNotLanded => .uncertain

def durableAfter (before proposed : Ledger) : Publication → Ledger
  | .acknowledged | .lostAckLanded => proposed
  | .rejected | .lostAckNotLanded => before

inductive Readback where
  | resolved (outcome : Outcome)
  | unrecorded | unavailable | collision
  deriving DecidableEq, Repr

def readback (ledger : Ledger) (available : Bool) (identity : Nat) (command : Command) : Readback :=
  if !available then .unavailable
  else match ledger.receipts identity with
    | none => .unrecorded
    | some receipt => if receipt.command = command then .resolved receipt.outcome else .collision

theorem uncertainty_does_not_identify_rollback :
    acknowledgement .lostAckLanded = .uncertain ∧
    acknowledgement .lostAckNotLanded = .uncertain := by decide

theorem confirmed_rejection_preserves_the_old_ledger (before proposed : Ledger) :
    durableAfter before proposed .rejected = before := rfl

theorem unavailable_readback_is_not_absence (ledger : Ledger) (identity : Nat) (command : Command) :
    readback ledger false identity command = .unavailable := rfl

theorem lost_acknowledgement_is_resolved_by_its_receipt (ledger : Ledger)
    (identity : Nat) (command : Command) (absent : ledger.receipts identity = none) :
    readback (durableAfter ledger (execute ledger identity command).ledger .lostAckLanded)
      true identity command = .resolved (plan ledger.focus command).outcome := by
  simp [readback, durableAfter, execute, absent]

theorem unlanded_write_has_no_receipt (ledger : Ledger) (identity : Nat)
    (command : Command) (absent : ledger.receipts identity = none) :
    readback (durableAfter ledger (execute ledger identity command).ledger .lostAckNotLanded)
      true identity command = .unrecorded := by
  simp [readback, durableAfter, absent]

def usage100 : Usage := { input := .known 100, output := .known 7 }
def usage101 : Usage := { input := .known 101, output := .known 7 }
def initial : Ledger := {}
def finishCommand := Command.finish "attempt" "answer" usage100
def first := execute initial 1 finishCommand
def second := execute first.ledger 2 (.recordUsage "attempt" usage100)
def third := execute second.ledger 3 (.recordUsage "attempt" usage101)
def staleState : Ledger := { initial with focus := { initial.focus with lease := some ("other", .active) } }
def stale := execute staleState 1 finishCommand
def conflictingState : Ledger := { initial with focus := { initial.focus with usage := some usage101 } }
def conflictCompletion := execute conflictingState 1 finishCommand
def otherAnswer := execute first.ledger 4 (.finish "attempt" "another-answer" usage100)
def changedAfterCompletion : Ledger := { first.ledger with focus := staleState.focus }
def replay := execute changedAfterCompletion 1 finishCommand
def alreadyCompleted := execute first.ledger 8 finishCommand

def usageLabel : UsageStatus → String
  | .accepted => "accepted"
  | .conflict => "conflict"
def outcomeLabel : Outcome → String
  | .completed usage => "completed:" ++ usageLabel usage
  | .alreadyCompleted usage => "already-completed:" ++ usageLabel usage
  | .usageRecorded usage => "recorded:" ++ usageLabel usage
  | .notOwned usage => "not-owned:" ++ usageLabel usage
  | .answerConflict usage => "answer-conflict:" ++ usageLabel usage
  | .refused _ => "refused"
def replyLabel : Reply → String
  | .committed outcome => outcomeLabel outcome
  | .replayed outcome => "replayed:" ++ outcomeLabel outcome
  | .collision => "collision"

def trace : String := "NATIVE_PROVIDER_TRACE " ++ String.intercalate " "
  ([first, second, third, stale, conflictCompletion, otherAnswer, replay, alreadyCompleted].map fun event => replyLabel event.reply)

end Mettapedia.Machines.NativeProviderDomain

#eval IO.println Mettapedia.Machines.NativeProviderDomain.trace
