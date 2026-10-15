import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceDebt

/-!
# Finite saturation of the actual occurrence frontier

Fresh representative visits strictly reduce the source-derived finite
carrier. Every other microstep reduces the uniquely determined residual
task debt. Both accounts are proof-only: running a bounded search never
evaluates the remaining search in order to construct its continuation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

structure Admitted (request : Request) : Prop where
  compiled : request.plan = compile request.plan.snapshot request.plan.permissions
  accepted : request.plan.complete = true
  rootSorted : OpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
    request.bound request.expected request.root

theorem fromSnapshot_admitted {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (accepted : (compile snapshot permissions).complete = true)
    (typed : HasType snapshot.language snapshot.free bound source expected)
    (object : isObjectPattern source = true) (scopeSafe : source.isWellScopedAt bound.length = true) :
    Admitted (Request.fromSnapshot snapshot permissions bound expected source) :=
  ⟨rfl, accepted, GeneralEquationCanonical.open_typed_erase typed object scopeSafe⟩

theorem Admitted.representative_within {request : Request} (admitted : Admitted request)
    (representative : Representative request) : representative.pattern ∈ request.universe := by
  have root := sourceUniverse_contains_source _ _ _ _ _ request.providerTerms admitted.rootSorted
  have accepted : (compile request.plan.snapshot request.plan.permissions).complete = true :=
    admitted.compiled ▸ admitted.accepted
  have related : Relation.EqvGen
      (GeneralEquationReverseBounds.Equation (compile request.plan.snapshot request.plan.permissions)
        request.bound request.expected) request.root representative.pattern := by
    rw [← admitted.compiled]
    exact representative.justified.equivalent
  have carrier := GeneralEquationReverseBounds.compiled_equivalence_universe_iff
    (root := request.root) request.providerTerms accepted related
  simpa only [← admitted.compiled, Request.universe] using carrier.mp root

def remainingPatterns (request : Request) (visited : List (Representative request)) : List Pattern :=
  request.universe.filter fun pattern => !(visited.map Representative.pattern).contains pattern

theorem remainingPatterns_visit (request : Request) (visited : List (Representative request))
    (representative : Representative request) :
    remainingPatterns request (visited ++ [representative]) =
      (remainingPatterns request visited).filter fun pattern => pattern != representative.pattern := by
  unfold remainingPatterns
  simp only [List.map_append, List.map_cons, List.map_nil, List.contains_append,
    List.contains_cons, List.contains_nil, Bool.or_false, List.filter_filter]
  congr 1
  funext pattern
  simp only [bne, Bool.not_or, Bool.and_comm]

theorem remainingPatterns_visit_decreases {request : Request} (admitted : Admitted request)
    (visited : List (Representative request)) (representative : Representative request)
    (fresh : (visited.map Representative.pattern).contains representative.pattern = false) :
    (remainingPatterns request (visited ++ [representative])).length <
      (remainingPatterns request visited).length := by
  rw [remainingPatterns_visit]
  apply List.length_filter_lt_length_iff_exists.mpr
  refine ⟨representative.pattern, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨admitted.representative_within representative, by rw [fresh]; rfl⟩
  · simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true]

noncomputable def State.rank (request : Request) (state : State request) : Nat × Nat :=
  ((remainingPatterns request state.visited).length, tasksDebt request state.agenda)

theorem expand_visits_other (request : Request) (state : State request) (task : Task request)
    (other : ∀ representative, task ≠ .visit representative) :
    (expand request state task).visits = [] := by
  cases task with
  | visit representative => exact False.elim (other representative rfl)
  | incoming representative edges =>
      cases edges with
      | nil => rfl
      | cons edge remaining =>
          by_cases backward : representative.pattern = edge.receipt.target
          · simp only [expand, dif_pos backward]
          · by_cases forward : representative.pattern = edge.source
            · simp only [expand, dif_neg backward, dif_pos forward]
            · simp only [expand, dif_neg backward, dif_neg forward]
  | «universe» => rfl
  | scanUniverse remaining => cases remaining <;> rfl
  | rule frame => simp only [expand, expandRule]; split <;> (try split) <;> rfl
  | equation frame => simp only [expand, expandEquation]; split <;> (try split) <;> rfl

theorem tick_rank_without_visit (request : Request) (state : State request)
    (task : Task request) (remaining : List (Task request))
    (agenda : state.agenda = task :: remaining) (same : (expand request state task).visits = []) :
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((tick request state).rank request) (state.rank request) := by
  have less := expand_debt_without_visit request state task same
  have sameVisited : (tick request state).visited = state.visited := by
    simp only [tick, agenda, same, List.append_nil]
  unfold State.rank
  rw [sameVisited]
  apply Prod.Lex.right
  simp only [tick, agenda, tasksDebt_append, tasksDebt_cons]
  omega

theorem tick_rank {request : Request} (admitted : Admitted request)
    (state : State request) (pending : state.agenda ≠ []) :
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((tick request state).rank request) (state.rank request) := by
  cases agenda : state.agenda with
  | nil => exact False.elim (pending agenda)
  | cons task remaining =>
      cases task with
      | visit representative =>
          by_cases seen : (state.visited.map Representative.pattern).contains representative.pattern = true
          · apply tick_rank_without_visit request state (.visit representative) remaining agenda
            simp only [expand, if_pos seen]
          · have fresh := Bool.eq_false_iff.mpr seen
            have less := remainingPatterns_visit_decreases admitted state.visited representative fresh
            apply Prod.Lex.left
            simpa only [State.rank, tick, agenda, expand, if_neg seen] using less
      | incoming representative edges =>
          apply tick_rank_without_visit request state (.incoming representative edges) remaining agenda
          exact expand_visits_other request state _ (fun _ impossible => by cases impossible)
      | «universe» =>
          apply tick_rank_without_visit request state .universe remaining agenda
          exact expand_visits_other request state _ (fun _ impossible => by cases impossible)
      | scanUniverse patterns =>
          apply tick_rank_without_visit request state (.scanUniverse patterns) remaining agenda
          exact expand_visits_other request state _ (fun _ impossible => by cases impossible)
      | equation frame =>
          apply tick_rank_without_visit request state (.equation frame) remaining agenda
          exact expand_visits_other request state _ (fun _ impossible => by cases impossible)
      | rule frame =>
          apply tick_rank_without_visit request state (.rule frame) remaining agenda
          exact expand_visits_other request state _ (fun _ impossible => by cases impossible)

def drain (request : Request) (admitted : Admitted request) (state : State request) :
    {finished : State request // finished.agenda = [] ∧ ∃ fuel, run request fuel state = finished} :=
  if idle : state.agenda = [] then
    ⟨state, idle, 0, rfl⟩
  else
    let finished := drain request admitted (tick request state)
    ⟨finished.val, finished.property.1, by
      obtain ⟨fuel, same⟩ := finished.property.2
      exact ⟨fuel + 1, same⟩⟩
termination_by state.rank request
decreasing_by exact tick_rank admitted state idle

def finish (request : Request) (admitted : Admitted request) : State request :=
  (drain request admitted (start request)).val

theorem finish_settled (request : Request) (admitted : Admitted request) :
    (finish request admitted).agenda = [] :=
  (drain request admitted (start request)).property.1

theorem finish_actual_run (request : Request) (admitted : Admitted request) :
    ∃ fuel, run request fuel (start request) = finish request admitted :=
  (drain request admitted (start request)).property.2

theorem finite_saturation (request : Request) (admitted : Admitted request) :
    ∃ fuel, settled request (run request fuel (start request)) = true := by
  obtain ⟨fuel, same⟩ := finish_actual_run request admitted
  refine ⟨fuel, ?_⟩
  rw [same]
  exact List.isEmpty_iff.mpr (finish_settled request admitted)

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
