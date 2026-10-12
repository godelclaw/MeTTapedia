import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

/-!+# Exact outer cursor transitions

These equations expose the actual publication, continuation and archival
steps while retaining their dependent source and occurrence evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

theorem expandEquation_found (request : Request) (state : State request) (frame : EquationFrame request)
    (answer : GeneralEquationJobExecution.Answer (equationRequest request frame.source frame.job))
    (found : frame.state.answers[frame.cursor]? = some answer) :
    expandEquation request state frame =
      { tasks := edgeDiscoveries request state ⟨frame.source, answer.val, answer.property⟩ ++
          [.equation {frame with cursor := frame.cursor + 1}]
        edges := [⟨frame.source, answer.val, answer.property⟩] } := by
  unfold expandEquation
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i other observed
    have same := Option.some.inj (found.symm.trans observed)
    subst other
    rfl

theorem expandEquation_closed (request : Request) (state : State request) (frame : EquationFrame request)
    (missing : frame.state.answers[frame.cursor]? = none)
    (closed : GeneralEquationJobExecution.settled frame.state = true) :
    expandEquation request state frame =
      { checkedEquations := [⟨frame, closed, missing⟩]
        unresolved := frame.state.unresolved.map Obligation.equation } := by
  unfold expandEquation
  split
  · split
    · rfl
    · contradiction
  · rename_i other observed
    rw [missing] at observed
    cases observed

theorem expandEquation_pending (request : Request) (state : State request) (frame : EquationFrame request)
    (missing : frame.state.answers[frame.cursor]? = none)
    (pending : GeneralEquationJobExecution.settled frame.state ≠ true) :
    expandEquation request state frame =
      { tasks := [.equation {frame with
          state := GeneralEquationJobExecution.tick (equationRequest request frame.source frame.job) frame.state
          reachable := .tick frame.reachable}] } := by
  unfold expandEquation
  split
  · split
    · contradiction
    · rfl
  · rename_i other observed
    rw [missing] at observed
    cases observed

theorem expandRule_found (request : Request) (frame : RuleFrame request)
    (answer : GeneralRuleJobExecution.Answer (ruleRequest request frame.representative frame.job))
    (found : frame.state.answers[frame.cursor]? = some answer) :
    expandRule request frame =
      { tasks := [.rule {frame with cursor := frame.cursor + 1}]
        answers := [⟨⟨frame.representative.pattern, frame.representative.conversions, answer.val⟩,
          frame.representative.justified, answer.property⟩] } := by
  unfold expandRule
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i other observed
    have same := Option.some.inj (found.symm.trans observed)
    subst other
    rfl

theorem expandRule_closed (request : Request) (frame : RuleFrame request)
    (missing : frame.state.answers[frame.cursor]? = none)
    (closed : GeneralRuleJobExecution.settled frame.state = true) :
    expandRule request frame =
      { checkedRules := [⟨frame, closed, missing⟩]
        unresolved := frame.state.unresolved.map Obligation.rule } := by
  unfold expandRule
  split
  · split
    · rfl
    · contradiction
  · rename_i other observed
    rw [missing] at observed
    cases observed

theorem expandRule_pending (request : Request) (frame : RuleFrame request)
    (missing : frame.state.answers[frame.cursor]? = none)
    (pending : GeneralRuleJobExecution.settled frame.state ≠ true) :
    expandRule request frame =
      { tasks := [.rule {frame with
          state := GeneralRuleJobExecution.tick (ruleRequest request frame.representative frame.job) frame.state
          reachable := .tick frame.reachable}] } := by
  unfold expandRule
  split
  · split
    · contradiction
    · rfl
  · rename_i other observed
    rw [missing] at observed
    cases observed

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
