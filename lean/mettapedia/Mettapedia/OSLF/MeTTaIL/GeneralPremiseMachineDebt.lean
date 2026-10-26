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

variable {matcher : MatchingExecution}

theorem query_expand_answers_length (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request matcher) :
    (Query.expand environment request task).answers.length ≤ 1 := by
  cases task with
  | start =>
      simp only [Query.expand]
      split
      · simp
      · split <;> simp
  | rows frame =>
      simp only [Query.expand]
      split
      · simp
      · split <;> simp
  | dynamicInputs frame =>
      simp only [Query.expand, Query.expandDynamicInputs]
      split
      · split <;> simp
      · split <;> simp
      · simp
      · simp
  | dynamicRows frame =>
      simp only [Query.expand, Query.expandDynamicRows]
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
    (state : Query.State environment request matcher) :
    (Query.tick environment request state).answers.length ≤ state.answers.length + 1 := by
  cases agenda : state.agenda with
  | nil => simp only [Query.tick, Scheduler.tick, agenda]; omega
  | cons task tasks =>
      have emitted := query_expand_answers_length environment request task
      simp only [Query.tick, Scheduler.tick, agenda, List.length_append]
      omega

def queryDebt (cost : matcher.CursorCost) (environment : Environment) (request : Query.Request)
    (state : Query.State environment request matcher) (cursor : Nat) : Nat :=
  2 * Query.agendaCost cost environment request state.agenda +
    (state.answers.length - cursor) + 1

theorem queryDebt_cursor (cost : matcher.CursorCost) (environment : Environment) (request : Query.Request)
    (state : Query.State environment request matcher) (cursor : Nat)
    (answer : Query.Answer environment request matcher)
    (found : state.answers[cursor]? = some answer) :
    queryDebt cost environment request state (cursor + 1) < queryDebt cost environment request state cursor := by
  have within := (List.getElem?_eq_some_iff.mp found).1
  simp only [queryDebt]
  omega

theorem queryDebt_tick (cost : matcher.CursorCost) (environment : Environment) (request : Query.Request)
    (state : Query.State environment request matcher) (cursor : Nat)
    (consumed : state.answers[cursor]? = none) (pending : state.agenda ≠ []) :
    queryDebt cost environment request (Query.tick environment request state) cursor <
      queryDebt cost environment request state cursor := by
  have within := List.getElem?_eq_none_iff.mp consumed
  have decreases := Query.tick_cost cost environment request state pending
  have emitted := query_tick_answers_length environment request state
  simp only [queryDebt]
  omega

#print axioms query_expand_answers_length
#print axioms query_tick_answers_length
#print axioms queryDebt
#print axioms queryDebt_cursor
#print axioms queryDebt_tick

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
