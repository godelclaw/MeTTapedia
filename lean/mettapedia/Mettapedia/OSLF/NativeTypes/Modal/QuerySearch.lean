import Mettapedia.OSLF.NativeTypes.Semantics.Operational

open Mettapedia.OSLF.Framework

/-!
# Modal queries stop after a discriminating execution

This runner uses the existing occurrence frontier's transitions. Possibility
stops after an accepted receipt; an outgoing universal stops after a rejected
receipt. A stopped query retains its pending agenda and every receipt already
emitted. The resulting state is an actual finite prefix of frontier execution,
and stopping does not supply an exhaustive certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.QuerySearch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Semantics.Operational GSLTTypeSynthesis

/-- The witness polarities can finish without inspecting the whole universe. -/
def evidenceFound (kind : ModalQuery) (request : Request) (test : Pattern → Bool)
    (state : State request) : Bool :=
  match kind with
  | .possibility => (targets request state).any test
  | .outgoingUniversal => !(targets request state).all test

/-- Interruptible execution freezes the exact frontier state at the first
stopping observation. It neither clears pending tasks nor changes receipts. -/
def runUntil (request : Request) (stop : State request → Bool) :
    Nat → State request → State request
  | 0, state => state
  | budget + 1, state =>
      if stop state then state else runUntil request stop budget (tick request state)

theorem runUntil_of_stop (request : Request) (stop : State request → Bool)
    (state : State request) (stopped : stop state = true) (budget : Nat) :
    runUntil request stop budget state = state := by
  cases budget <;> simp [runUntil, stopped]

/-- A paused query resumes with the same predicate and the same actual state. -/
theorem runUntil_add (request : Request) (stop : State request → Bool)
    (first second : Nat) (state : State request) :
    runUntil request stop (first + second) state =
      runUntil request stop second (runUntil request stop first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, runUntil]
  | succ first ih =>
      by_cases stopped : stop state = true
      · simp only [Nat.succ_add, runUntil, stopped, if_true]
        exact (runUntil_of_stop request stop state stopped second).symm
      · simp only [Nat.succ_add, runUntil, if_neg stopped]
        exact ih (tick request state)

/-- The stopped runner is a genuine execution prefix. Every preceding
transition was necessary because its stopping observation was false. -/
theorem runUntil_execution_prefix (request : Request) (stop : State request → Bool)
    (budget : Nat) (state : State request) :
    ∃ used, used ≤ budget ∧
      runUntil request stop budget state = run request used state ∧
      (∀ earlier, earlier < used → stop (run request earlier state) = false) ∧
      (used = budget ∨ stop (runUntil request stop budget state) = true) := by
  induction budget generalizing state with
  | zero =>
      refine ⟨0, Nat.le_refl _, rfl, ?_, Or.inl rfl⟩
      intro earlier impossible
      omega
  | succ budget ih =>
      by_cases stopped : stop state = true
      · refine ⟨0, Nat.zero_le _, ?_, ?_, Or.inr ?_⟩
        · simp only [runUntil, stopped, if_true, run]
        · intro earlier impossible
          omega
        · rw [runUntil, if_pos stopped]
          exact stopped
      · obtain ⟨used, bounded, executed, before, final⟩ := ih (tick request state)
        refine ⟨used + 1, by omega, ?_, ?_, ?_⟩
        · simp only [runUntil, if_neg stopped, run]
          exact executed
        · intro earlier shorter
          cases earlier with
          | zero => simpa only [run] using Bool.eq_false_iff.mpr stopped
          | succ earlier =>
              simpa only [run] using before earlier (by omega)
        · rcases final with exhausted | witnessed
          · exact Or.inl (by omega)
          · exact Or.inr (by simpa only [runUntil, if_neg stopped] using witnessed)

theorem runUntil_reachable {request : Request} {stop : State request → Bool}
    {state : State request} (reached : Reachable request state) (budget : Nat) :
    Reachable request (runUntil request stop budget state) := by
  obtain ⟨used, _, executed, _, _⟩ := runUntil_execution_prefix request stop budget state
  rw [executed]
  exact reachable_run reached used

/-- Already emitted occurrences remain in their original order and retain
their complete dependent origins, even when endpoints coincide. -/
theorem runUntil_answers_prefix (request : Request) (stop : State request → Bool)
    (budget : Nat) (state : State request) :
    GeneralPremise.Scheduler.Prefix state.answers
      (runUntil request stop budget state).answers := by
  obtain ⟨used, _, executed, _, _⟩ := runUntil_execution_prefix request stop budget state
  rw [executed]
  exact answers_prefix request used state

theorem runUntil_work_bounds (request : Request) (stop : State request → Bool)
    (budget : Nat) (state : State request) :
    state.work ≤ (runUntil request stop budget state).work ∧
      (runUntil request stop budget state).work ≤ state.work + budget := by
  obtain ⟨used, bounded, executed, _, _⟩ := runUntil_execution_prefix request stop budget state
  rw [executed]
  have actual := run_work_bounds request used state
  exact ⟨actual.1, actual.2.trans (Nat.add_le_add_left bounded state.work)⟩

/-- More budget cannot move past an already found discriminating receipt. -/
theorem runUntil_after_evidence (request : Request) (stop : State request → Bool)
    (first more : Nat) (state : State request)
    (found : stop (runUntil request stop first state) = true) :
    runUntil request stop (first + more) state = runUntil request stop first state := by
  rw [runUntil_add]
  exact runUntil_of_stop request stop _ found more

def search (kind : ModalQuery) (request : Request) (test : Pattern → Bool)
    (budget : Nat) (state : State request) : State request :=
  runUntil request (evidenceFound kind request test) budget state

theorem search_resume (kind : ModalQuery) (request : Request) (test : Pattern → Bool)
    (first second : Nat) (state : State request) :
    search kind request test (first + second) state =
      search kind request test second (search kind request test first state) :=
  runUntil_add request _ first second state

theorem found_evidence_readout {kind : ModalQuery} {request : Request}
    {test : Pattern → Bool} {state : State request}
    (found : evidenceFound kind request test state = true) :
    modalReadout kind request state test =
      .decided (match kind with | .possibility => true | .outgoingUniversal => false) := by
  cases kind <;> unfold evidenceFound at found <;>
    simp only [modalReadout, found, if_true]

/-- Stopping after evidence never converts pending work into coverage. -/
theorem stopped_pending_remains_incomplete {kind : ModalQuery} {request : Request}
    {test : Pattern → Bool} {budget : Nat} {state : State request}
    (pending : (search kind request test budget state).agenda ≠ []) :
    complete request (search kind request test budget state) = false :=
  pending_not_complete request _ pending

end Mettapedia.OSLF.NativeTypes.Modal.QuerySearch

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
open Mettapedia.OSLF.NativeTypes.Modal.QuerySearch

def Generated.searchModal (generated : Generated) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (kind : ModalQuery)
    (test : InvariantTest (generated.request bound expected source)) (budget : Nat) :
    QueryRun generated bound expected source :=
  let request := generated.request bound expected source
  let state := search kind request test.accepts budget (start request)
  let enabled := match kind with
    | .possibility => generated.logicFragment.core.possibility
    | .outgoingUniversal => generated.logicFragment.core.modal
  {state := state, result :=
    if !enabled then match kind with
      | .possibility => .refusedPossibility
      | .outgoingUniversal => .refused .modal
    else match generated.equationAdmission with
      | some true => modalReadout kind request state test.accepts
      | some false => .rejectedCube
      | none => .unknown}

end Mettapedia.OSLF.NativeTypes.Generation

namespace Mettapedia.OSLF.NativeTypes.Modal.QuerySearch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Semantics.Operational GSLTTypeSynthesis

/-- The accelerated checker returns the same state and answer as the original
checker at an earned execution prefix, including refusals and unknown. -/
theorem searchModal_actual_prefix (generated : Generated) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (kind : ModalQuery)
    (test : InvariantTest (generated.request bound expected source)) (budget : Nat) :
    ∃ used, used ≤ budget ∧
      generated.searchModal bound expected source kind test budget =
        generated.checkModal bound expected source kind test used := by
  obtain ⟨used, bounded, executed, _, _⟩ := runUntil_execution_prefix
    (generated.request bound expected source) (evidenceFound kind _ test.accepts) budget (start _)
  refine ⟨used, bounded, ?_⟩
  simp only [Generated.searchModal, search, executed, Generated.checkModal, Generated.execute]
  rfl

theorem searchModal_sound {generated : Generated} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {kind : ModalQuery}
    {test : InvariantTest (generated.request bound expected source)} {budget : Nat} {answer : Bool}
    (read : (generated.searchModal bound expected source kind test budget).result = .decided answer) :
    answer = true ↔ ModalHolds kind (generated.request bound expected source) test.accepts := by
  obtain ⟨used, _, actual⟩ := searchModal_actual_prefix generated bound expected source kind test budget
  rw [actual] at read
  exact generated_modal_readout_correct read

theorem searchModal_native_sound {generated : Generated} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {kind : ModalQuery}
    {test : InvariantTest (generated.request bound expected source)} {budget : Nat} {answer : Bool}
    (read : (generated.searchModal bound expected source kind test budget).result = .decided answer) :
    answer = true ↔
      (gsltOSLF (theory generated bound expected)).satisfies
        (generated.request bound expected source).root
        (questionType kind (generated.request bound expected source) test).pred := by
  obtain ⟨used, _, actual⟩ := searchModal_actual_prefix generated bound expected source kind test budget
  rw [actual] at read
  exact generated_answer_is_native_membership read

end Mettapedia.OSLF.NativeTypes.Modal.QuerySearch

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Semantics.Operational

/-- Both conclusive answers retain the independently specified modal meaning.
Search may stop at one witness, whereas `checkModal` collects its whole budget. -/
theorem generated_search_modal_correct {generated : Generated} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {kind : ModalQuery}
    {test : InvariantTest (generated.request bound expected source)} {budget : Nat} {answer : Bool}
    (read : (generated.searchModal bound expected source kind test budget).result = .decided answer) :
    answer = true ↔ ModalHolds kind (generated.request bound expected source) test.accepts :=
  Mettapedia.OSLF.NativeTypes.Modal.QuerySearch.searchModal_sound read

theorem generated_search_answer_is_native_membership {generated : Generated} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {kind : ModalQuery}
    {test : InvariantTest (generated.request bound expected source)} {budget : Nat} {answer : Bool}
    (read : (generated.searchModal bound expected source kind test budget).result = .decided answer) :
    answer = true ↔
      (gsltOSLF (theory generated bound expected)).satisfies
        (generated.request bound expected source).root
        (questionType kind (generated.request bound expected source) test).pred :=
  Mettapedia.OSLF.NativeTypes.Modal.QuerySearch.searchModal_native_sound read

theorem searchModal_zero (generated : Generated) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (kind : ModalQuery)
    (test : InvariantTest (generated.request bound expected source)) :
    generated.searchModal bound expected source kind test 0 =
      generated.checkModal bound expected source kind test 0 := rfl

end Mettapedia.OSLF.NativeTypes.Generation
