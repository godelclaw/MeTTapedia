import Mettapedia.Logic.DerivationGraph.CheckedCursor
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.Machines.OutcomeRunner

/-!
# Retained proof checking as an existing answer machine

One worker step checks one supplied source address through the existing
source-indexed checked cursor. Success keeps the new checked prefix; refusal keeps
the previous cursor and the complete refused suffix. Completion requires an
empty schedule. The occurrence-preserving answer-machine adapter supplies
budgeted execution, resumption and the retained observation history.
The final report retains its terminal work independently of that history;
check-only execution can discard the accumulated journal without dropping
the checked prefix or refused head and suffix.

The worker checks a supplied finite schedule. It does not search for proofs,
erase failed unused rows, or restart a checked prefix on resumption. Physical
owner and cursor representations remain implementation refinements.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ProofChecking

open Mettapedia.Logic Mettapedia.Logic.DerivationGraph
open Mettapedia.Logic.DerivationGraph.BorrowedCursor
open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {J Origin : Type} {rules : List J → J → Prop}

inductive Status where
  | running
  | complete
  | refused
  deriving DecidableEq

structure Work (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) where
  cursor : CheckedCursor interface store
  pending : List NodeId
  accepted : Nat
  status : Status

def start {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (cursor : CheckedCursor interface store) (schedule : List NodeId) : Work interface store :=
  ⟨cursor, schedule, 0, .running⟩

def tick {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin} :
    Work interface store → Option (Work interface store)
  | ⟨cursor, pending, count, .running⟩ =>
      match pending with
      | [] => some ⟨cursor, [], count, .complete⟩
      | source :: later =>
          match cursor.advance [source] with
          | none => some ⟨cursor, pending, count, .refused⟩
          | some checked => some ⟨checked, later, count + 1, .running⟩
  | _ => none

def verdict {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin} :
    Work interface store → Option Bool
  | ⟨_, pending, _, .complete⟩ => if pending.isEmpty then some true else none
  | ⟨_, _, _, .refused⟩ => some false
  | _ => none

/-- The final working state remains owned by the result. Its Boolean is an
observation of that state, not a substitute for the retained checked prefix. -/
structure Report (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) where
  private mk ::
  work : Work interface store
  accepted : Bool
  valid : verdict work = some accepted

def answer {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (work : Work interface store) : Option (Report interface store) :=
  match observed : verdict work with
  | none => none
  | some accepted => some ⟨work, accepted, observed⟩

theorem answer_spec {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (work : Work interface store) (report : Report interface store)
    (observed : answer work = some report) :
    report.work = work ∧ verdict work = some report.accepted := by
  unfold answer at observed
  split at observed
  · cases observed
  · rename_i accepted checked
    cases Option.some.inj observed
    exact ⟨rfl, checked⟩

def completedVerdict {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin} :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
      (Work interface store) (Report interface store) Empty → Option Bool
  | .finished report => some report.accepted
  | _ => none

abbrev answerCore (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) :
    AnswerMachineCore (CheckedCursor interface store × List NodeId) (Report interface store) where
  State := Work interface store
  load input := start input.1 input.2
  step := tick
  answer := answer
  answer_final := by
    intro work report observed
    have checked := (answer_spec work report observed).2
    rcases work with ⟨cursor, pending, count, status⟩
    cases status <;> simp_all [verdict, tick]

def machine (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) :
    Machine (Work interface store) (ProductiveCoreAdapters.Occurrence (Work interface store))
      (Report interface store) Empty :=
  ProductiveCoreAdapters.answerMachine (answerCore interface store)

theorem advance_one_state {interface : RuleWitness.{0, 0} rules}
    {store : Store J interface.W Origin} (cursor : CheckedCursor interface store) (source : NodeId) :
    (cursor.advance [source]).map CheckedCursor.state =
      BorrowedCursor.step interface store cursor.state source := by
  rw [CheckedCursor.advance_state]
  simp [BorrowedCursor.run]

theorem tick_refuses {interface : RuleWitness.{0, 0} rules}
    {store : Store J interface.W Origin} (cursor : CheckedCursor interface store)
    (source : NodeId) (later : List NodeId) (count : Nat)
    (refused : cursor.advance [source] = none) :
    tick (⟨cursor, source :: later, count, .running⟩ : Work interface store) =
      some ⟨cursor, source :: later, count, .refused⟩ := by
  simp [tick, refused]

/-- The accumulated counter and remaining suffix describe actual generic
cursor execution from the supplied initial checked value. -/
def Meaning {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (initial : CheckedCursor interface store) (schedule : List NodeId)
    (work : Work interface store) : Prop :=
  ∃ consumed, schedule = consumed ++ work.pending ∧
    BorrowedCursor.run interface store initial.state consumed = some work.cursor.state ∧
    work.accepted = consumed.length ∧
    (work.status = .complete → work.pending = []) ∧
    (work.status = .refused → ∃ source later, work.pending = source :: later ∧
      BorrowedCursor.step interface store work.cursor.state source = none)

theorem start_meaning {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (initial : CheckedCursor interface store) (schedule : List NodeId) :
    Meaning initial schedule (start initial schedule) := by
  refine ⟨[], rfl, rfl, rfl, ?_, ?_⟩ <;> simp [start]

theorem tick_meaning {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (initial : CheckedCursor interface store) (schedule : List NodeId)
    (before after : Work interface store) (meaning : Meaning initial schedule before)
    (stepped : tick before = some after) : Meaning initial schedule after := by
  obtain ⟨consumed, partition, executed, count, complete, refused⟩ := meaning
  rcases before with ⟨cursor, pending, accepted, status⟩
  cases status with
  | complete | refused => simp [tick] at stepped
  | running =>
      cases pending with
      | nil =>
          cases Option.some.inj stepped
          exact ⟨consumed, partition, executed, count, fun _ => rfl, by simp⟩
      | cons source later =>
          cases checked : cursor.advance [source] with
          | none =>
              have failed : BorrowedCursor.step interface store cursor.state source = none := by
                simpa [checked] using (advance_one_state cursor source).symm
              have shape : (⟨cursor, source :: later, accepted, .refused⟩ : Work interface store) = after := by
                simpa [tick, checked] using stepped
              subst after
              exact ⟨consumed, partition, executed, count, by simp,
                fun _ => ⟨source, later, rfl, failed⟩⟩
          | some next =>
              have successful : BorrowedCursor.run interface store cursor.state [source] =
                  some next.state := by
                simpa [checked] using (CheckedCursor.advance_state cursor [source]).symm
              have shape : (⟨next, later, accepted + 1, .running⟩ : Work interface store) = after := by
                simpa [tick, checked] using stepped
              subst after
              refine ⟨consumed ++ [source], ?_, ?_, ?_, by simp, by simp⟩
              · simpa [List.append_assoc] using partition
              · rw [BorrowedCursor.run_append, executed, Option.bind_some]
                exact successful
              · simpa using count

private theorem reachable_invariant {Input : Type} (core : MachineCore Input)
    (invariant : core.State → Prop)
    (preserved : ∀ before after, invariant before → core.StepRel before after → invariant after)
    {before after : core.State} (reachable : core.Steps before after) :
    invariant before → invariant after := by
  induction reachable using Relation.ReflTransGen.head_induction_on with
  | refl => exact id
  | head step _ ih => intro initial; exact ih (preserved _ _ initial step)

theorem reachable_meaning (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (initial : CheckedCursor interface store) (schedule : List NodeId) (work : Work interface store)
    (reachable : (answerCore interface store).toMachineCore.Steps (start initial schedule) work) :
    Meaning initial schedule work :=
  reachable_invariant (answerCore interface store).toMachineCore (Meaning initial schedule)
    (tick_meaning initial schedule) reachable (start_meaning initial schedule)

/-- A true final observation requires the supplied schedule to have been
consumed completely; a valid earlier root cannot hide a failed unused row. -/
theorem completed_run (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (initial : CheckedCursor interface store) (schedule : List NodeId) (work : Work interface store)
    (meaning : Meaning initial schedule work) (observed : verdict work = some true) :
    work.pending = [] ∧ work.accepted = schedule.length ∧
      BorrowedCursor.run interface store initial.state schedule = some work.cursor.state := by
  obtain ⟨consumed, partition, executed, count, complete, _⟩ := meaning
  rcases work with ⟨cursor, pending, accepted, status⟩
  cases status with
  | running | refused => simp [verdict] at observed
  | complete =>
      have empty : pending = [] := complete rfl
      subst pending
      have same : schedule = consumed := by simpa using partition
      exact ⟨rfl, by simpa [same] using count, by simpa [same] using executed⟩

theorem refused_run (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (initial : CheckedCursor interface store) (schedule : List NodeId) (work : Work interface store)
    (meaning : Meaning initial schedule work) (observed : verdict work = some false) :
    BorrowedCursor.run interface store initial.state schedule = none := by
  obtain ⟨consumed, partition, executed, _, _, failed⟩ := meaning
  rcases work with ⟨cursor, pending, accepted, status⟩
  cases status with
  | running => simp [verdict] at observed
  | complete => simp [verdict] at observed
  | refused =>
      rw [partition, BorrowedCursor.run_append, executed, Option.bind_some]
      obtain ⟨source, later, pendingShape, rejected⟩ := failed rfl
      change pending = source :: later at pendingShape
      change BorrowedCursor.step interface store cursor.state source = none at rejected
      rw [pendingShape]
      simp [BorrowedCursor.run, rejected]

theorem finished_true_sound (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (initial : CheckedCursor interface store) (schedule : List NodeId)
    (finished : ∃ fuel events report, (machine interface store).run fuel (start initial schedule) =
      (events, .finished report) ∧ report.accepted = true) :
    ∃ work : Work interface store, work.pending = [] ∧ work.accepted = schedule.length ∧
      BorrowedCursor.run interface store initial.state schedule = some work.cursor.state := by
  obtain ⟨fuel, events, report, completed, accepted⟩ := finished
  obtain ⟨work, reachable, observed⟩ :=
    (ProductiveCoreAdapters.answer_reachable_iff_finished
      (answerCore interface store) (start initial schedule) report).mpr ⟨fuel, events, completed⟩
  exact ⟨work, completed_run interface store initial schedule work
    (reachable_meaning interface store initial schedule work reachable)
    (by simpa [accepted] using (answer_spec work report observed).2)⟩

theorem finished_false_sound (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (initial : CheckedCursor interface store) (schedule : List NodeId)
    (finished : ∃ fuel events report, (machine interface store).run fuel (start initial schedule) =
      (events, .finished report) ∧ report.accepted = false) :
    BorrowedCursor.run interface store initial.state schedule = none := by
  obtain ⟨fuel, events, report, completed, accepted⟩ := finished
  obtain ⟨work, reachable, observed⟩ :=
    (ProductiveCoreAdapters.answer_reachable_iff_finished
      (answerCore interface store) (start initial schedule) report).mpr ⟨fuel, events, completed⟩
  exact refused_run interface store initial schedule work
    (reachable_meaning interface store initial schedule work reachable)
    (by simpa [accepted] using (answer_spec work report observed).2)

/-- An accepted supplied schedule constructs an actual machine trace with
one checking step per source row and one final completion step. -/
theorem complete_trace (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (initial : CheckedCursor interface store) (schedule : List NodeId) (count : Nat)
    (result : BorrowedCursor.State J)
    (executed : BorrowedCursor.run interface store initial.state schedule = some result) :
    ∃ final : CheckedCursor interface store,
      ∃ events : List (ProductiveCoreAdapters.Occurrence (Work interface store)),
      final.state = result ∧ events.length = schedule.length + 1 ∧
      ProductiveCoreAdapters.Trace (answerCore interface store).toMachineCore
        ⟨initial, schedule, count, .running⟩ events
        ⟨final, [], count + schedule.length, .complete⟩ := by
  induction schedule generalizing initial count with
  | nil =>
      refine ⟨initial, [(⟨initial, [], count, .running⟩, ⟨initial, [], count, .complete⟩)],
        Option.some.inj executed, rfl, ?_⟩
      exact .cons rfl (.empty _)
  | cons source later ih =>
      cases first : BorrowedCursor.step interface store initial.state source with
      | none => simp [BorrowedCursor.run, first] at executed
      | some nextState =>
          have remaining : BorrowedCursor.run interface store nextState later = some result := by
            simpa [BorrowedCursor.run, first] using executed
          cases checked : initial.advance [source] with
          | none =>
              have absent := advance_one_state initial source
              simp [checked, first] at absent
          | some next =>
              have same : next.state = nextState := by
                have actual := advance_one_state initial source
                simpa [checked, first] using actual
              have continuing : BorrowedCursor.run interface store next.state later = some result := by
                rw [same]
                exact remaining
              obtain ⟨final, events, resultState, length, trace⟩ := ih next (count + 1) continuing
              refine ⟨final,
                (⟨initial, source :: later, count, .running⟩,
                  ⟨next, later, count + 1, .running⟩) :: events,
                resultState, by simp [length], ?_⟩
              have stepped : tick (⟨initial, source :: later, count, .running⟩ : Work interface store) =
                  some ⟨next, later, count + 1, .running⟩ := by simp [tick, checked]
              exact .cons stepped (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace)

/-- The existing answer machine accepts exactly the full generic source run.
An accepted root in a shorter prefix cannot satisfy this observation. -/
theorem finished_true_iff (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (initial : CheckedCursor interface store) (schedule : List NodeId) :
    (∃ fuel events report, (machine interface store).run fuel (start initial schedule) =
      (events, .finished report) ∧ report.accepted = true) ↔
      ∃ result, BorrowedCursor.run interface store initial.state schedule = some result := by
  constructor
  · intro finished
    obtain ⟨work, _, _, executed⟩ := finished_true_sound interface store initial schedule finished
    exact ⟨work.cursor.state, executed⟩
  · rintro ⟨result, executed⟩
    obtain ⟨final, events, _, _, trace⟩ := complete_trace interface store initial schedule 0 result executed
    let terminal : Work interface store := ⟨final, [], 0 + schedule.length, .complete⟩
    let report : Report interface store := ⟨terminal, true, rfl⟩
    exact ⟨events.length + 1, events, report,
      ProductiveCoreAdapters.trace_answer_finish (answerCore interface store) trace rfl, rfl⟩

theorem run_add (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (first extra : Nat) (work : Work interface store) :
    (machine interface store).run (first + extra) work =
      (machine interface store).continueRun extra ((machine interface store).run first work) :=
  Machine.run_add _ _ _ _

theorem events_prefix (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (first extra : Nat) (work : Work interface store) :
    ((machine interface store).run first work).1.IsPrefix
      ((machine interface store).run (first + extra) work).1 := by
  rw [run_add]
  exact (machine interface store).continueRun_events_prefix _ _

/-- The check-only runner returns the same final report while omitting the
accumulated event journal. It therefore retains the reached terminal work. -/
theorem check_only_report_meaning (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) (initial : CheckedCursor interface store)
    (schedule : List NodeId) (fuel : Nat) (report : Report interface store)
    (completed : OutcomeRunner.run (machine interface store) fuel (start initial schedule) =
      .finished report) : Meaning initial schedule report.work := by
  have outcome : ((machine interface store).run fuel (start initial schedule)).2 =
      .finished report :=
    (OutcomeRunner.run_eq (machine interface store) fuel (start initial schedule)).symm.trans completed
  have finished : ∃ events, (machine interface store).run fuel (start initial schedule) =
      (events, .finished report) := ⟨_, Prod.ext rfl outcome⟩
  obtain ⟨events, ran⟩ := finished
  obtain ⟨work, reachable, observed⟩ :=
    (ProductiveCoreAdapters.answer_reachable_iff_finished
      (answerCore interface store) (start initial schedule) report).mpr ⟨fuel, events, ran⟩
  rw [(answer_spec work report observed).1]
  exact reachable_meaning interface store initial schedule work reachable

theorem refused_report_status {interface : RuleWitness.{0, 0} rules}
    {store : Store J interface.W Origin} (report : Report interface store)
    (refused : report.accepted = false) : report.work.status = .refused := by
  have observed : verdict report.work = some false := by simpa [refused] using report.valid
  generalize workIs : report.work = work at observed ⊢
  rcases work with ⟨cursor, pending, count, status⟩
  cases status <;> simp_all [verdict]

/-- A completed refusal retains the actual accepted prefix and its checked
cursor, together with the failed head and every following source address.
This statement needs no event history in its result. -/
theorem check_only_refusal_retains (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) (initial : CheckedCursor interface store)
    (schedule : List NodeId) (fuel : Nat) (report : Report interface store)
    (completed : OutcomeRunner.run (machine interface store) fuel (start initial schedule) =
      .finished report) (refused : report.accepted = false) :
    ∃ consumed source later,
      schedule = consumed ++ source :: later ∧ report.work.pending = source :: later ∧
      BorrowedCursor.run interface store initial.state consumed = some report.work.cursor.state ∧
      report.work.accepted = consumed.length ∧ report.work.status = .refused ∧
      BorrowedCursor.step interface store report.work.cursor.state source = none := by
  obtain ⟨consumed, partition, executed, count, _, failed⟩ :=
    check_only_report_meaning interface store initial schedule fuel report completed
  have status := refused_report_status report refused
  obtain ⟨source, later, pending, rejected⟩ := failed status
  exact ⟨consumed, source, later, by simpa [pending] using partition,
    pending, executed, count, status, rejected⟩

/-- Budget splitting preserves the entire terminal report, including the
retained checked cursor and residual suffix; no journal is reconstructed. -/
theorem check_only_run_add (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) (first extra : Nat) (work : Work interface store) :
    OutcomeRunner.run (machine interface store) (first + extra) work =
      OutcomeRunner.resume (machine interface store) extra
        (OutcomeRunner.run (machine interface store) first work) :=
  OutcomeRunner.run_add _ _ _ _

theorem check_only_completed_stable (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) (extra : Nat) (report : Report interface store) :
    OutcomeRunner.resume (machine interface store) extra (.finished report) = .finished report := rfl

theorem check_only_accepts_iff (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) (initial : CheckedCursor interface store)
    (schedule : List NodeId) :
    (∃ fuel, completedVerdict
      (OutcomeRunner.run (machine interface store) fuel (start initial schedule)) = some true) ↔
      ∃ result, BorrowedCursor.run interface store initial.state schedule = some result := by
  constructor
  · rintro ⟨fuel, observed⟩
    cases outcome : OutcomeRunner.run (machine interface store) fuel (start initial schedule) with
    | finished report =>
        have accepted : report.accepted = true := by simpa [completedVerdict, outcome] using observed
        have actual := (OutcomeRunner.run_eq (machine interface store) fuel
          (start initial schedule)).symm.trans outcome
        exact (finished_true_iff interface store initial schedule).mp
          ⟨fuel, _, report, Prod.ext rfl actual, accepted⟩
    | _ => simp [completedVerdict, outcome] at observed
  · intro checked
    obtain ⟨fuel, events, report, completed, accepted⟩ :=
      (finished_true_iff interface store initial schedule).mpr checked
    exact ⟨fuel, by simp [OutcomeRunner.run_eq, completed, completedVerdict, accepted]⟩

namespace Controls

private abbrev controlRules (premises : List Nat) (conclusion : Nat) : Prop :=
  (premises = [] ∧ conclusion = 0) ∨ (premises = [0, 0] ∧ conclusion = 1)

private def interface : RuleWitness controlRules where
  W := Unit
  isInstance _ premises conclusion := decide (controlRules premises conclusion)
  sound _ _ _ accepted := of_decide_eq_true accepted
  complete _ _ valid := ⟨(), decide_eq_true valid⟩

private def store : Store Nat interface.W Unit where
  revision := 0
  read source :=
    if source = 0 then some ⟨0, (), [], ()⟩ else
    if source = 1 then some ⟨1, (), [0, 0], ()⟩ else
    if source = 2 then some ⟨2, (), [], ()⟩ else
    if source = 3 then some ⟨0, (), [], ()⟩ else none

private def initial : CheckedCursor interface store := CheckedCursor.begin interface store

theorem duplicate_premises_accepted :
    completedVerdict ((machine interface store).run 4 (start initial [0, 1])).2 = some true := by
  rfl

private def inspect (outcome : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Work interface store) (Report interface store) Empty) :
    Option (List NodeId × Nat × Status × Option Nat) :=
  match outcome with
  | .exhausted work =>
      some (work.pending, work.accepted, work.status,
        (work.cursor.root 1).map CheckedJudgment.judgment)
  | _ => none

theorem last_checked_row_is_not_yet_completion :
    inspect ((machine interface store).run 2 (start initial [0, 1])).2 =
      some ([], 2, .running, some 1) := by
  rfl

/-- The valid earlier root is retained, but the failed row and following
valid row are both still pending. They cannot disappear from batch checking. -/
theorem failed_unused_row_keeps_prefix_and_suffix :
    inspect ((machine interface store).run 3 (start initial [0, 1, 2, 3])).2 =
      some ([2, 3], 2, .refused, some 1) := by
  rfl

theorem valid_root_does_not_hide_unused_bad_row :
    completedVerdict ((machine interface store).run 4 (start initial [0, 1, 2, 3])).2 = some false := by
  rfl

theorem resume_keeps_rejected_suffix :
    (machine interface store).continueRun 1
      ((machine interface store).run 3 (start initial [0, 1, 2, 3])) =
    (machine interface store).run 4 (start initial [0, 1, 2, 3]) := by
  exact (run_add interface store 3 1 (start initial [0, 1, 2, 3])).symm

theorem finished_refusal_never_restarts :
    (machine interface store).continueRun 100
      ((machine interface store).run 4 (start initial [0, 1, 2, 3])) =
    (machine interface store).run 4 (start initial [0, 1, 2, 3]) := by
  rfl

theorem split_inside_checked_prefix :
    (machine interface store).continueRun 3 ((machine interface store).run 1 (start initial [0, 1])) =
      (machine interface store).run 4 (start initial [0, 1]) := by
  exact (run_add interface store 1 3 (start initial [0, 1])).symm

private def deduplicatedStore : Store Nat interface.W Unit :=
  { store with read := fun source => if source = 1 then some ⟨1, (), [0], ()⟩ else store.read source }

theorem deleting_a_duplicate_premise_is_refused :
    completedVerdict ((machine interface deduplicatedStore).run 4
      (start (CheckedCursor.begin interface deduplicatedStore) [0, 1])).2 = some false := by
  rfl

private def inspectCache (outcome : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Work interface store) (Report interface store) Empty) : Option (Array Nat) :=
  match outcome with
  | .exhausted work => some work.cursor.state.cache
  | _ => none

theorem equal_judgments_keep_distinct_source_occurrences :
    inspectCache ((machine interface store).run 2 (start initial [0, 3])).2 = some #[0, 0] := by
  rfl

theorem duplicate_schedule_address_is_refused :
    completedVerdict ((machine interface store).run 4 (start initial [0, 0])).2 = some false := by
  rfl

private def inspectCompleted (outcome : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Work interface store) (Report interface store) Empty) :
    Option (Bool × List NodeId × Nat × Status × Option Nat) :=
  match outcome with
  | .finished report =>
      some (report.accepted, report.work.pending, report.work.accepted, report.work.status,
        (report.work.cursor.root 1).map CheckedJudgment.judgment)
  | _ => none

/-- The prefix and refused suffix are read directly from the completed
check-only result. No operational event list is retained or inspected. -/
theorem check_only_completed_refusal_keeps_state :
    inspectCompleted (OutcomeRunner.run (machine interface store) 4 (start initial [0, 1, 2, 3])) =
      some (false, [2, 3], 2, .refused, some 1) := by
  rfl

theorem check_only_completed_success_keeps_root :
    inspectCompleted (OutcomeRunner.run (machine interface store) 4 (start initial [0, 1])) =
      some (true, [], 2, .complete, some 1) := by
  rfl

theorem check_only_refusal_split_exact :
    OutcomeRunner.resume (machine interface store) 1
      (OutcomeRunner.run (machine interface store) 3 (start initial [0, 1, 2, 3])) =
      OutcomeRunner.run (machine interface store) 4 (start initial [0, 1, 2, 3]) := by
  exact (check_only_run_add interface store 3 1 (start initial [0, 1, 2, 3])).symm

theorem check_only_completed_refusal_never_restarts :
    OutcomeRunner.resume (machine interface store) 100
      (OutcomeRunner.run (machine interface store) 4 (start initial [0, 1, 2, 3])) =
      OutcomeRunner.run (machine interface store) 4 (start initial [0, 1, 2, 3]) := by
  rfl

private def inspectCompletedCache (outcome : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Work interface store) (Report interface store) Empty) :
    Option (Array Nat) :=
  match outcome with
  | .finished report => some report.work.cursor.state.cache
  | _ => none

theorem check_only_equal_judgments_keep_occurrences :
    inspectCompletedCache (OutcomeRunner.run (machine interface store) 4 (start initial [0, 3])) =
      some #[0, 0] := by
  rfl

end Controls

end Mettapedia.Machines.Cursor.ProofChecking
