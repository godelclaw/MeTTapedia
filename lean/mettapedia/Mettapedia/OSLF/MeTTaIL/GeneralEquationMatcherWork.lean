import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobCoverage

/-!
# Exhausting the real scoped matcher in equation coverage proofs

This explicit completion strategy follows the actual small-step matcher until
its agenda is empty. Its structural work measure is earned from the matcher
syntax, and the resulting list retains every trace and answer position.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open GeneralScopedMatchMachine

def finishMatcher (request : GeneralScopedMatchMachine.Request) (state : GeneralScopedMatchMachine.State) :
    GeneralScopedMatchMachine.State :=
  if _finished : GeneralScopedMatchMachine.complete state then state
  else finishMatcher request (GeneralScopedMatchMachine.tick request state)
termination_by agendaCost request state.agenda
decreasing_by exact tick_cost (request := request) (Bool.eq_false_iff.mpr _finished)

theorem finishMatcher_complete (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) :
    GeneralScopedMatchMachine.complete (finishMatcher request state) = true := by
  rw [finishMatcher.eq_def]
  split
  next finished => exact finished
  next pending =>
    have decrease := tick_cost (request := request) (Bool.eq_false_iff.mpr pending)
    exact finishMatcher_complete request (GeneralScopedMatchMachine.tick request state)
termination_by agendaCost request state.agenda
decreasing_by assumption

theorem finishMatcher_reachable {request : GeneralScopedMatchMachine.Request}
    {state : GeneralScopedMatchMachine.State} (reached : GeneralScopedMatchMachine.Reachable request state) :
    GeneralScopedMatchMachine.Reachable request (finishMatcher request state) := by
  rw [finishMatcher.eq_def]
  split
  next finished => exact reached
  next pending =>
    have decrease := tick_cost (request := request) (Bool.eq_false_iff.mpr pending)
    exact finishMatcher_reachable (GeneralScopedMatchMachine.reachable_tick reached)
termination_by agendaCost request state.agenda
decreasing_by assumption

theorem finishMatcher_finished (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) (finished : GeneralScopedMatchMachine.complete state = true) :
    finishMatcher request state = state := by
  rw [finishMatcher.eq_def, dif_pos finished]

theorem finishMatcher_tick (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) (pending : GeneralScopedMatchMachine.complete state = false) :
    finishMatcher request (GeneralScopedMatchMachine.tick request state) = finishMatcher request state := by
  rw [finishMatcher.eq_def request state, dif_neg (Bool.eq_false_iff.mp pending)]

theorem matcher_tick_prefix (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) :
    GeneralPremise.Scheduler.Prefix state.answers (GeneralScopedMatchMachine.tick request state).answers := by
  cases agenda : state.agenda with
  | nil => simpa only [GeneralScopedMatchMachine.tick, agenda] using GeneralPremise.Scheduler.Prefix.refl state.answers
  | cons work rest =>
      cases tasks : work.tasks with
      | nil => exact ⟨[⟨work.assignment, work.trace⟩], by simp only [GeneralScopedMatchMachine.tick, agenda, tasks]⟩
      | cons task tasks =>
          simpa only [GeneralScopedMatchMachine.tick, agenda, tasks] using GeneralPremise.Scheduler.Prefix.refl state.answers

theorem finishMatcher_prefix (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) :
    GeneralPremise.Scheduler.Prefix state.answers (finishMatcher request state).answers := by
  rw [finishMatcher.eq_def]
  split
  next finished => exact GeneralPremise.Scheduler.Prefix.refl _
  next pending =>
    have decrease := tick_cost (request := request) (Bool.eq_false_iff.mpr pending)
    exact (matcher_tick_prefix request state).trans
      (finishMatcher_prefix request (GeneralScopedMatchMachine.tick request state))
termination_by agendaCost request state.agenda
decreasing_by assumption

theorem finishMatcher_answer_at (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) (cursor : Nat) (answer : GeneralScopedMatchMachine.Answer)
    (found : state.answers[cursor]? = some answer) :
    (finishMatcher request state).answers[cursor]? = some answer := by
  obtain ⟨future, same⟩ := finishMatcher_prefix request state
  rw [same, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem finishMatcher_answers_iff {request : GeneralScopedMatchMachine.Request}
    {state : GeneralScopedMatchMachine.State} (reached : GeneralScopedMatchMachine.Reachable request state)
    (answer : GeneralScopedMatchMachine.Answer) :
    answer ∈ (finishMatcher request state).answers ↔ answer.Valid request :=
  complete_answers_iff (finishMatcher_reachable reached) (finishMatcher_complete request state) answer

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
