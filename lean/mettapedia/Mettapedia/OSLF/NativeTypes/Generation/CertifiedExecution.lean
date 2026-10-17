import Mettapedia.OSLF.NativeTypes.Generation.BindingReadoutLaws

/-!
# Replay-certified operational sessions

A session retains the actual matcher and premise state together with its
proved replay from the installed executor's initial agenda. Negative and
outgoing-universal answers use this provenance and the independently proved
occurrence coverage. An arbitrary empty scheduler state is not a session.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed.CertifiedExecution

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent

variable (installed : BindingPipeline.Installed)

structure Session (source : Installed.Source) where
  budget : Nat
  state : installed.ExecutionState source
  replay : state = installed.resume source budget (installed.begin source)

def begin (source : Installed.Source) : Session installed source :=
  ⟨0, installed.begin source, rfl⟩

private theorem resume_idle (source : Installed.Source) (state : installed.ExecutionState source)
    (drained : state.agenda = []) (fuel : Nat) : installed.resume source fuel state = state := by
  change Scheduler.run _ fuel state = state
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Scheduler.run, Scheduler.tick_idle _ _ drained]
      exact ih

namespace Session

variable {installed} {source : Installed.Source}

@[ext] theorem ext (first second : Session installed source)
    (sameBudget : first.budget = second.budget) (sameState : first.state = second.state) :
    first = second := by
  cases first
  cases second
  cases sameBudget
  cases sameState
  rfl

def resume (session : Session installed source) (fuel : Nat) : Session installed source where
  budget := session.budget + fuel
  state := installed.resume source fuel session.state
  replay := by rw [session.replay, ← installed.resume_add]

@[simp] theorem resume_state (session : Session installed source) (fuel : Nat) :
    (session.resume fuel).state = installed.resume source fuel session.state := rfl

@[simp] theorem resume_budget (session : Session installed source) (fuel : Nat) :
    (session.resume fuel).budget = session.budget + fuel := rfl

theorem resume_add (session : Session installed source) (first second : Nat) :
    session.resume (first + second) = (session.resume first).resume second := by
  apply ext
  · exact (Nat.add_assoc _ _ _).symm
  · exact installed.resume_add source first second session.state

def receipts (session : Session installed source) := installed.receipts session.state

theorem receipts_preserved (session : Session installed source) (fuel : Nat) :
    Scheduler.Prefix session.receipts (session.resume fuel).receipts :=
  installed.receipts_preserved source fuel session.state

def complete (session : Session installed source) : Bool := Scheduler.complete session.state

def possibility (session : Session installed source) (predicate : Pattern → Bool) : Installed.Answer :=
  installed.possibility source predicate session.state

def outgoingAll (session : Session installed source) (predicate : Pattern → Bool) : Installed.Answer :=
  installed.outgoingAll source predicate session.state

def absence (session : Session installed source) : Installed.Answer :=
  match session.possibility (fun _ => true) with
  | .proved => .refuted
  | .refuted => .proved
  | .unknown => .unknown

theorem stable_state (session : Session installed source)
    (completed : session.complete = true) (fuel : Nat) :
    (session.resume fuel).state = session.state :=
  resume_idle installed source session.state ((Scheduler.complete_iff _).mp completed).1 fuel

theorem stable_readouts (session : Session installed source)
    (completed : session.complete = true) (fuel : Nat) (predicate : Pattern → Bool) :
    (session.resume fuel).possibility predicate = session.possibility predicate ∧
      (session.resume fuel).outgoingAll predicate = session.outgoingAll predicate ∧
      (session.resume fuel).absence = session.absence := by
  have stable := session.stable_state completed fuel
  simp only [possibility, outgoingAll, absence, stable, and_self]

theorem possibility_proved (session : Session installed source) (predicate : Pattern → Bool)
    (proved : session.possibility predicate = .proved) :
    ∃ target, installed.HasSuccessor source target ∧ predicate target = true :=
  installed.possibility_proved source predicate session.state proved

theorem possibility_refuted (session : Session installed source) (predicate : Pattern → Bool)
    (refuted : session.possibility predicate = .refuted) :
    ∀ target, installed.HasSuccessor source target → predicate target = false := by
  apply installed.possibility_refuted source predicate session.budget
  simpa only [possibility, session.replay] using refuted

theorem outgoingAll_refuted (session : Session installed source) (predicate : Pattern → Bool)
    (refuted : session.outgoingAll predicate = .refuted) :
    ∃ target, installed.HasSuccessor source target ∧ predicate target = false :=
  installed.outgoingAll_refuted source predicate session.state refuted

theorem outgoingAll_proved (session : Session installed source) (predicate : Pattern → Bool)
    (proved : session.outgoingAll predicate = .proved) :
    ∀ target, installed.HasSuccessor source target → predicate target = true := by
  apply installed.outgoingAll_proved source predicate session.budget
  simpa only [outgoingAll, session.replay] using proved

theorem absence_proved (session : Session installed source)
    (proved : session.absence = .proved) :
    ∀ target, ¬ installed.HasSuccessor source target := by
  unfold absence at proved
  cases value : session.possibility (fun _ => true) with
  | proved => simp only [value, reduceCtorEq] at proved
  | refuted =>
      intro target possible
      have contradiction := session.possibility_refuted (fun _ => true) value target possible
      cases contradiction
  | unknown => simp only [value, reduceCtorEq] at proved

theorem absence_refuted (session : Session installed source)
    (refuted : session.absence = .refuted) :
    ∃ target, installed.HasSuccessor source target := by
  unfold absence at refuted
  cases value : session.possibility (fun _ => true) with
  | proved =>
      obtain ⟨target, possible, _⟩ := session.possibility_proved (fun _ => true) value
      exact ⟨target, possible⟩
  | refuted => simp only [value, reduceCtorEq] at refuted
  | unknown => simp only [value, reduceCtorEq] at refuted

theorem unfinished_empty_unknown (session : Session installed source)
    (empty : session.receipts = []) (unfinished : session.complete = false)
    (predicate : Pattern → Bool) :
    session.possibility predicate = .unknown ∧ session.outgoingAll predicate = .unknown ∧
      session.absence = .unknown := by
  have readings := installed.unfinished_empty_unknown source predicate session.state empty unfinished
  have positive := (installed.unfinished_empty_unknown source (fun _ => true)
    session.state empty unfinished).1
  exact ⟨readings.1, readings.2, by simp only [absence, possibility, positive]⟩

theorem successors_exact (session : Session installed source)
    (completed : session.complete = true) (target : Pattern) :
    target ∈ session.receipts.map (·.target) ↔ installed.HasSuccessor source target := by
  have drained := ((Scheduler.complete_iff session.state).mp completed).1
  rw [session.replay] at drained
  simpa only [receipts, session.replay] using
    installed.drained_successors source session.budget drained target

theorem receipt_covered (session : Session installed source)
    (completed : session.complete = true)
    (answer : Execution.RootAnswer installed.Environment source.bound source.type source.term) :
    answer ∈ session.receipts := by
  have drained := ((Scheduler.complete_iff session.state).mp completed).1
  rw [session.replay] at drained
  simpa only [receipts, session.replay, Installed.receipts, Installed.resume, Installed.begin] using
    Scheduled.drained_receipts_complete installed.Environment installed.structural
      source.bound source.type source.term session.budget drained answer

theorem occurrences_exact (session : Session installed source)
    (completed : session.complete = true) (index : Nat)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured final : ScopedRuleMatching.Assignment) (history : List Event) (target : Pattern) :
    (∃ answer ∈ session.receipts,
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = final ∧ answer.history = history ∧ answer.target = target) ↔
    RootFiring installed.Environment source.bound source.type source.term
      index trace captured final history target := by
  constructor
  · rintro ⟨answer, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact answer.valid
  · intro valid
    exact ⟨⟨index, trace, captured, final, history, target, valid⟩,
      session.receipt_covered completed _, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Session

def finish (source : Installed.Source) : Session installed source where
  budget := Scheduled.completeBudget installed.Environment source.bound source.type source.term
  state := installed.finish source
  replay := Scheduled.finishSource_is_run installed.Environment source.bound source.type source.term

theorem finish_drained (source : Installed.Source) : (finish installed source).state.agenda = [] :=
  Scheduled.finish_settled installed.Environment (Scheduled.sourceGoal installed.Environment
    source.bound source.type source.term)

theorem finish_occurrences (source : Installed.Source) (index : Nat)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured final : ScopedRuleMatching.Assignment) (history : List Event) (target : Pattern) :
    (∃ answer ∈ (finish installed source).receipts,
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = final ∧ answer.history = history ∧ answer.target = target) ↔
    RootFiring installed.Environment source.bound source.type source.term
      index trace captured final history target :=
  Scheduled.finishSource_occurrences installed.Environment installed.structural
    source.bound source.type source.term index trace captured final history target

namespace Session

variable {installed} {source : Installed.Source}

/-- Continue the retained session with a computed bound on the complete
initial transition tree. Already emitted receipts remain in their order. -/
def finish (session : Session installed source) : Session installed source :=
  session.resume (Scheduled.completeBudget installed.Environment source.bound source.type source.term)

theorem finish_state (session : Session installed source) :
    session.finish.state = (CertifiedExecution.finish installed source).state := by
  unfold Session.finish
  rw [resume_state, session.replay, ← installed.resume_add]
  rw [Nat.add_comm, installed.resume_add]
  exact resume_idle installed source (CertifiedExecution.finish installed source).state
    (finish_drained installed source) session.budget

theorem finish_receipts_preserved (session : Session installed source) :
    Scheduler.Prefix session.receipts session.finish.receipts := session.receipts_preserved _

theorem finish_drained (session : Session installed source) : session.finish.state.agenda = [] := by
  rw [session.finish_state]
  exact CertifiedExecution.finish_drained installed source

end Session

/-- This raw state has no provenance from the declared initial agenda. -/
def forged (source : Installed.Source) : installed.ExecutionState source := {}

theorem forged_raw_readouts (source : Installed.Source) :
    Scheduler.complete (forged installed source) = true ∧
      installed.possibility source (fun _ => true) (forged installed source) = .refuted ∧
      installed.outgoingAll source (fun _ => false) (forged installed source) = .proved := by
  exact ⟨rfl, rfl, rfl⟩

/-- A real outgoing step distinguishes a forged empty tray from an earned
complete result. No valid session can expose that forged state. -/
theorem forged_not_reachable (source : Installed.Source) {target : Pattern}
    (actual : installed.HasSuccessor source target) (budget : Nat) :
    installed.resume source budget (installed.begin source) ≠ forged installed source := by
  intro forgedReplay
  have drained : (installed.resume source budget (installed.begin source)).agenda = [] := by
    rw [forgedReplay]
    rfl
  have found := (installed.drained_successors source budget drained target).mpr actual
  rw [forgedReplay] at found
  exact List.not_mem_nil found

theorem no_forged_session (source : Installed.Source) {target : Pattern}
    (actual : installed.HasSuccessor source target) (session : Session installed source) :
    session.state ≠ forged installed source := by
  rw [session.replay]
  exact forged_not_reachable installed source actual session.budget

theorem actual_successor_prevents_absence (source : Installed.Source) {target : Pattern}
    (actual : installed.HasSuccessor source target) (session : Session installed source) :
    session.absence ≠ .proved := by
  intro claimed
  exact session.absence_proved claimed target actual

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed.CertifiedExecution
