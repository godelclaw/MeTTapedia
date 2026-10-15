import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

/-!
# Retained admission and universe-scan obligations

A successful source gate starts the finite-universe scan. Every microstep
retains that scan or records its completion, so a reachable settled frontier
has actually finished it. Static admission failures are distinguished from
runtime equation and premise obligations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

def UniverseAccounted (request : Request) (state : State request) : Prop :=
  state.universeScanned = true ∨ .universe ∈ state.agenda ∨
    ∃ remaining, .scanUniverse remaining ∈ state.agenda

theorem source_gate {request : Request}
    (typed : HasType request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.source request.expected)
    (object : isObjectPattern request.source = true)
    (scope : request.source.isWellScopedAt request.bound.length = true) :
    checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true :=
  checkOpenPatternWellSorted_complete (GeneralEquationCanonical.open_typed_erase typed object scope)

theorem start_universe_accounted (request : Request)
    (checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true) : UniverseAccounted request (start request) := by
  simp only [UniverseAccounted, start, checked, if_true]
  exact .inr (.inl (List.mem_cons_of_mem _ List.mem_cons_self))

theorem tick_universe_accounted (request : Request) (state : State request)
    (accounted : UniverseAccounted request state) : UniverseAccounted request (tick request state) := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using accounted
  | cons head rest =>
      rcases accounted with done | initialScan | ⟨remaining, scan⟩
      · left
        simp only [tick, agenda, done, Bool.true_or]
      · rcases List.mem_cons.mp (agenda ▸ initialScan) with current | later
        · subst head
          right
          right
          refine ⟨request.universe, ?_⟩
          simp only [tick, agenda, expand, List.mem_append, List.mem_singleton]
          exact .inl trivial
        · right
          left
          simp only [tick, agenda]
          exact List.mem_append_right _ later
      · rcases List.mem_cons.mp (agenda ▸ scan) with current | later
        · subst head
          cases remaining with
          | nil =>
              left
              simp only [tick, agenda, expand, Bool.or_true]
          | cons source remaining =>
              right
              right
              refine ⟨remaining, ?_⟩
              simp only [tick, agenda, expand, List.mem_append, List.mem_singleton]
              exact .inl (.inr trivial)
        · right
          right
          refine ⟨remaining, ?_⟩
          simp only [tick, agenda]
          exact List.mem_append_right _ later

theorem reachable_universe_accounted {request : Request} {state : State request}
    (checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true)
    (reached : Reachable request state) : UniverseAccounted request state := by
  induction reached with
  | start => exact start_universe_accounted request checked
  | tick reached ih => exact tick_universe_accounted request _ ih

theorem settled_universe_scanned {request : Request} {state : State request}
    (checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true)
    (reached : Reachable request state) (idle : settled request state = true) :
    state.universeScanned = true := by
  have empty : state.agenda = [] := List.isEmpty_iff.mp idle
  rcases reachable_universe_accounted checked reached with done | initialScan | ⟨remaining, scan⟩
  · exact done
  · rw [empty] at initialScan
    exact False.elim (List.not_mem_nil initialScan)
  · rw [empty] at scan
    exact False.elim (List.not_mem_nil scan)

theorem settled_empty_complete {request : Request} {state : State request}
    (checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true)
    (reached : Reachable request state) (idle : settled request state = true)
    (resolved : state.unresolved = []) : complete request state = true := by
  have scanned := settled_universe_scanned checked reached idle
  simp only [complete, show state.agenda.isEmpty = true from idle, resolved,
    List.isEmpty_nil, scanned, Bool.and_self]

def InitialFailure : Obligation → Bool
  | .admission _ | .sourceRejected => true
  | .equation _ | .rule _ => false

def NoInitialFailure (request : Request) (state : State request) : Prop :=
  ∀ reason ∈ state.unresolved, InitialFailure reason = false

theorem start_obligations_empty (request : Request)
    (accepted : request.plan.complete = true)
    (checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true) : (start request).unresolved = [] := by
  have empty : request.plan.obligations = [] := List.isEmpty_iff.mp accepted
  simp only [start, checked, if_true, empty, List.map_nil]

theorem expansion_no_initial_failure (request : Request) (state : State request) (task : Task request) :
    ∀ reason ∈ (expand request state task).unresolved, InitialFailure reason = false := by
  intro reason member
  cases task with
  | visit representative =>
      simp only [expand] at member
      split at member <;> simp only [List.not_mem_nil] at member
  | incoming representative edges =>
      simp only [expand] at member
      split at member
      all_goals repeat' split at member
      all_goals simp only [List.not_mem_nil] at member
  | «universe» => simp only [expand, List.not_mem_nil] at member
  | scanUniverse remaining => cases remaining <;> simp only [expand, List.not_mem_nil] at member
  | equation frame =>
      simp only [expand, expandEquation] at member
      repeat' split at member
      all_goals try simp only [List.not_mem_nil] at member
      all_goals
        obtain ⟨actual, _, same⟩ := List.mem_map.mp member
        subst reason
        rfl
  | rule frame =>
      simp only [expand, expandRule] at member
      repeat' split at member
      all_goals try simp only [List.not_mem_nil] at member
      all_goals
        obtain ⟨actual, _, same⟩ := List.mem_map.mp member
        subst reason
        rfl

theorem tick_no_initial_failure (request : Request) (state : State request)
    (admitted : NoInitialFailure request state) : NoInitialFailure request (tick request state) := by
  intro reason member
  cases agenda : state.agenda with
  | nil => exact admitted reason (by simpa only [tick, agenda] using member)
  | cons task rest =>
      simp only [tick, agenda, List.mem_append] at member
      exact member.elim (admitted reason) (expansion_no_initial_failure request state task reason)

theorem reachable_no_initial_failure {request : Request} {state : State request}
    (accepted : request.plan.complete = true)
    (checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true) (reached : Reachable request state) :
    NoInitialFailure request state := by
  induction reached with
  | start =>
      intro reason member
      rw [start_obligations_empty request accepted checked] at member
      exact False.elim (List.not_mem_nil member)
  | tick reached ih => exact tick_no_initial_failure request _ ih

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
