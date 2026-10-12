import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCorrectness
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineTermination
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison

/-!
# Finite complete execution of scoped matcher tasks

The independently defined traced derivations characterize every completed
machine. Erasing those origins agrees with the original scoped matcher for
every schema, target, ambient context and initial assignment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

theorem emitted_matchAt {request : Request} {state : State} (reached : Reachable request state)
    {answer : Answer} (member : answer ∈ state.answers) :
    answer.assignment ∈ matchAt request.rule request.spec request.ambient request.site request.path
      request.depth request.initial request.schema request.target :=
  (answers_sound reached member).matching.complete

theorem complete_matching_iff {request : Request} {state : State} (reached : Reachable request state)
    (finished : complete state = true) (final : Assignment) :
    (∃ answer ∈ state.answers, answer.assignment = final) ↔
      final ∈ matchAt request.rule request.spec request.ambient request.site request.path
        request.depth request.initial request.schema request.target := by
  constructor
  · rintro ⟨answer, member, same⟩
    exact same ▸ emitted_matchAt reached member
  · intro matched
    obtain ⟨trace, traced⟩ := matches_trace (GeneralScopedMatch.matchAt_sound matched)
    exact ⟨{ assignment := final, trace }, answers_complete reached finished traced, rfl⟩

theorem completedEventually (request : Request) :
    ∃ fuel : Nat, complete (run request fuel (start request)) = true ∧
      ∀ answer, answer ∈ (run request fuel (start request)).answers ↔ answer.Valid request := by
  obtain ⟨fuel, finished⟩ := finiteDrain request (start request)
  exact ⟨fuel, finished, complete_answers_iff (reachable_run fuel .start) finished⟩

theorem answers_persist_tick (request : Request) (state : State) {answer : Answer}
    (member : answer ∈ state.answers) : answer ∈ (tick request state).answers := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using member
  | cons work rest =>
    cases tasks : work.tasks with
    | nil => simpa only [tick, agenda, tasks] using List.mem_append_left _ member
    | cons _ _ => simpa only [tick, agenda, tasks] using member

theorem answers_persist_run (request : Request) (state : State) (fuel : Nat) {answer : Answer}
    (member : answer ∈ state.answers) : answer ∈ (run request fuel state).answers := by
  induction fuel generalizing state with
  | zero => exact member
  | succ fuel ih => exact ih _ (answers_persist_tick request state member)

#print axioms run_add
#print axioms answers_sound
#print axioms answers_complete
#print axioms finiteDrain
#print axioms completedEventually
#print axioms complete_matching_iff

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine
