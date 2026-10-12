import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryTermination

/-!
# Earned work measures for suspended matcher cursors

Pending structural work and unread answers have different accounts. A tick
can publish at most one matcher answer, so twice the structural cost pays for
both that transition and its later answer delivery.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

def matcherDebt (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) (cursor : Nat) : Nat :=
  2 * GeneralScopedMatchMachine.agendaCost request state.agenda +
    (state.answers.length - cursor) + 1

theorem matcherDebt_cursor (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) (cursor : Nat)
    (answer : GeneralScopedMatchMachine.Answer)
    (found : state.answers[cursor]? = some answer) :
    matcherDebt request state (cursor + 1) < matcherDebt request state cursor := by
  have within := (List.getElem?_eq_some_iff.mp found).1
  simp only [matcherDebt]
  omega

theorem matcherDebt_tick (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) (cursor : Nat)
    (consumed : state.answers[cursor]? = none)
    (pending : GeneralScopedMatchMachine.complete state = false) :
    matcherDebt request (GeneralScopedMatchMachine.tick request state) cursor <
      matcherDebt request state cursor := by
  have within := List.getElem?_eq_none_iff.mp consumed
  have decreases := GeneralScopedMatchMachine.tick_cost (request := request) pending
  have emitted := GeneralScopedMatchMachine.tick_answers_length request state
  simp only [matcherDebt]
  omega

theorem query_expand_answers_length (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request) :
    (Query.expand environment request task).answers.length ≤ 1 := by
  cases task with
  | start =>
      simp only [Query.expand]
      split <;> simp
  | rows frame =>
      simp only [Query.expand]
      split
      · simp
      · split <;> simp
  | arguments frame =>
      simp only [Query.expand, Query.expandArguments]
      split
      · split <;> simp
      · rename_i _ _ _ _ mode _ _ _ _
        cases mode with
        | input =>
          dsimp only
          split
          · simp
          · split <;> simp
        | output => simp
      · simp
  | matcher frame =>
      simp only [Query.expand, Query.expandMatcher]
      split
      · simp
      · split <;> simp

theorem query_tick_answers_length (environment : Environment) (request : Query.Request)
    (state : Query.State environment request) :
    (Query.tick environment request state).answers.length ≤ state.answers.length + 1 := by
  cases agenda : state.agenda with
  | nil => simp only [Query.tick, Scheduler.tick, agenda]; omega
  | cons task tasks =>
      have emitted := query_expand_answers_length environment request task
      simp only [Query.tick, Scheduler.tick, agenda, List.length_append]
      omega

def queryDebt (environment : Environment) (request : Query.Request)
    (state : Query.State environment request) (cursor : Nat) : Nat :=
  2 * Query.agendaCost environment request state.agenda +
    (state.answers.length - cursor) + 1

theorem queryDebt_cursor (environment : Environment) (request : Query.Request)
    (state : Query.State environment request) (cursor : Nat)
    (answer : Query.Answer environment request)
    (found : state.answers[cursor]? = some answer) :
    queryDebt environment request state (cursor + 1) < queryDebt environment request state cursor := by
  have within := (List.getElem?_eq_some_iff.mp found).1
  simp only [queryDebt]
  omega

theorem queryDebt_tick (environment : Environment) (request : Query.Request)
    (state : Query.State environment request) (cursor : Nat)
    (consumed : state.answers[cursor]? = none) (pending : state.agenda ≠ []) :
    queryDebt environment request (Query.tick environment request state) cursor <
      queryDebt environment request state cursor := by
  have within := List.getElem?_eq_none_iff.mp consumed
  have decreases := Query.tick_cost environment request state pending
  have emitted := query_tick_answers_length environment request state
  simp only [queryDebt]
  omega

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
