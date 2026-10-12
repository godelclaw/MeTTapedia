import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCertified
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryCorrectness

/-!
# Complete finite matching and provider-query services

The work bound is computed from the actual finite continuation expansion.
It does not bound recursive rule calls; those are handled separately by
structural descent. Every matcher alternative and every provider occurrence
is retained with its independently checked semantic evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.FiniteServices

open ScopedRuleMatching

namespace Matcher

open GeneralScopedMatchMachine

theorem complete_at_cost (request : Request) (state : State) (fuel : Nat)
    (enough : agendaCost request state.agenda ≤ fuel) :
    complete (run request fuel state) = true := by
  induction fuel generalizing state with
  | zero =>
      cases agenda : state.agenda with
      | nil => simp only [run, complete, agenda, List.isEmpty_nil]
      | cons work rest =>
          have positive : 0 < agendaCost request state.agenda := by
            rw [agenda, agendaCost_cons, workCost_eq]
            omega
          omega
  | succ fuel ih =>
      by_cases finished : complete state = true
      · have noAgenda := List.isEmpty_iff.mp finished
        have stationary : tick request state = state := by simp [tick, noAgenda]
        change complete (run request fuel (tick request state)) = true
        rw [stationary]
        exact ih state (by simp [noAgenda, agendaCost_nil])
      · have decrease := tick_cost (request := request) (Bool.eq_false_iff.mpr finished)
        exact ih _ (by omega)

def state (request : Request) : State :=
  run request (agendaCost request (start request).agenda) (start request)

theorem state_complete (request : Request) : complete (state request) = true :=
  complete_at_cost request _ _ (Nat.le_refl _)

def answers (request : Request) : List {answer : Answer // answer.Valid request} :=
  (state request).answers.attach.map fun answer =>
    ⟨answer.val, answers_sound (reachable_run _ .start) answer.property⟩

theorem answers_complete (request : Request) (wanted : Answer)
    (valid : wanted.Valid request) :
    ∃ answer ∈ answers request, answer.val = wanted := by
  have listed : wanted ∈ (state request).answers :=
    GeneralScopedMatchMachine.answers_complete (reachable_run _ .start)
      (state_complete request) valid
  refine ⟨⟨wanted, valid⟩, ?_, rfl⟩
  exact List.mem_map.mpr ⟨⟨wanted, listed⟩, List.mem_attach _ _, rfl⟩

end Matcher

namespace Provider

open GeneralPremise GeneralPremise.Query

theorem settled_at_cost (environment : Environment) (request : Request)
    (state : State environment request) (fuel : Nat)
    (enough : agendaCost environment request state.agenda ≤ fuel) :
    (run environment request fuel state).agenda = [] := by
  induction fuel generalizing state with
  | zero =>
      cases agenda : state.agenda with
      | nil => simpa only [run, Scheduler.run] using agenda
      | cons task rest =>
          have positive : 0 < agendaCost environment request state.agenda := by
            rw [agenda, agendaCost_cons, taskCost_eq]
            omega
          omega
  | succ fuel ih =>
      change (run environment request fuel (tick environment request state)).agenda = []
      by_cases empty : state.agenda = []
      · have stationary : tick environment request state = state := by
          simp [tick, Scheduler.tick, empty]
        change (run environment request fuel (tick environment request state)).agenda = []
        rw [stationary]
        exact ih state (by simp [empty, agendaCost_nil])
      · have decrease := tick_cost environment request state empty
        change agendaCost environment request (tick environment request state).agenda + 1 =
          agendaCost environment request state.agenda at decrease
        exact ih _ (by omega)

def state (environment : Environment) (request : Request) : State environment request :=
  run environment request (agendaCost environment request (start environment request).agenda)
    (start environment request)

theorem state_settled (environment : Environment) (request : Request) :
    (state environment request).agenda = [] :=
  settled_at_cost environment request _ _ (Nat.le_refl _)

def answers (environment : Environment) (request : Request) : List (Answer environment request) :=
  (state environment request).answers

theorem answers_complete (environment : Environment) (request : Request)
    (wanted : Answer environment request) : wanted ∈ answers environment request :=
  GeneralPremise.Query.answers_complete environment request _ wanted
    (state_settled environment request)

end Provider

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.FiniteServices
