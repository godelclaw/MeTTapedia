import Mettapedia.OSLF.NativeTypes.Executable.Finite
import Mettapedia.OSLF.NativeTypes.Decision.FiniteGraphControls

/-!
# Public finite native-query controls

The finite tables are checked against independently specified event spans.
Besides directional and branching controls, a three-state cycle presentation
maps onto a two-state model with proved endpoint coverage. This is a concrete
covered observation; it does not claim a represented material-state quotient.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Finite.Controls

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Reference.Core (Outcome)

namespace Directional

abbrev table := FiniteGraph.Controls.table
def observed : FiniteMuCalculus.Environment (Fin 4) 1 := fun _ => {0, 1}

theorem past_refuted :
    ((check table (.box .past (.var 0)) observed 10 0).map Outcome.answer) = some (some false) := by
  decide +kernel

theorem future_proved :
    ((check table (.box .future (.var 0)) observed 10 0).map Outcome.answer) = some (some true) := by
  decide +kernel

theorem insufficient_allowance_unknown :
    ((check table (.box .future (.var 0)) observed 0 0).map Outcome.answer) = some none := by
  decide +kernel

theorem accepting_deadlock_refuted :
    ((check table (Formula.buchi .future) (fun _ => {1}) 1000 1).map Outcome.answer) = some (some false) := by
  decide +kernel

theorem nonaccepting_loop_refuted :
    ((check table (Formula.buchi .future) (fun _ => {1}) 1000 0).map Outcome.answer) = some (some false) := by
  decide +kernel

theorem accepting_loop_proved :
    ((check table (Formula.buchi .future) (fun _ => {0}) 1000 0).map Outcome.answer) = some (some true) := by
  decide +kernel

theorem nonpositive_binder_refused :
    (check table (.mu (.neg (.var 0))) (fun index : Fin 0 => index.elim0) 1000 0).isNone = true := by
  decide +kernel

end Directional

namespace Branching

def span : ReductionSpan (Fin 3) where
  Edge := Fin 4
  source event := if event = 0 ∨ event = 1 then 0 else if event = 2 then 1 else 2
  target event := if event = 0 ∨ event = 2 then 1 else 2

def table : FiniteGraph.Table span where
  edge source target := decide ((source = 0 ∧ (target = 1 ∨ target = 2)) ∨
    (source = 1 ∧ target = 1) ∨ (source = 2 ∧ target = 2))
  exact := by unfold span; decide +kernel

def accepting : FiniteMuCalculus.Environment (Fin 3) 1 := fun _ => {1}

theorem some_recurrent_path :
    ((check table (Formula.buchi .future) accepting 1000 0).map Outcome.answer) = some (some true) := by
  decide +kernel

theorem not_every_successor_has_recurrence :
    ((check table (.box .future (Formula.buchi .future)) accepting 1000 0).map Outcome.answer) =
      some (some false) := by decide +kernel

theorem existential_next_observation :
    ((check table (.diamond .future (.var 0)) accepting 10 0).map Outcome.answer) = some (some true) := by
  decide +kernel

theorem universal_next_observation_refuted :
    ((check table (.box .future (.var 0)) accepting 10 0).map Outcome.answer) = some (some false) := by
  decide +kernel

/-- The rejecting branch continues forever. The positive existential query
does not certify recurrence along every nondeterministic execution. -/
theorem rejecting_infinite_path :
    ∃ path : Nat → Fin 3, path 0 = 0 ∧
      (∀ index, (transitionSystem span).trans (path index) .future (path (index + 1))) ∧
      ∀ index, path index ∉ ({1} : Finset (Fin 3)) := by
  refine ⟨fun index => if index = 0 then 0 else 2, by decide, ?_, ?_⟩
  · intro index
    cases index with
    | zero => exact ⟨(1 : Fin 4), by decide, by decide⟩
    | succ index => exact ⟨(3 : Fin 4), by simp [span], by simp [span]⟩
  · intro index
    by_cases zero : index = 0 <;> simp [zero]

theorem existential_query_has_actual_path :
    BuchiPath (transitionSystem span) .future ({1} : Set (Fin 3)) 0 := by
  simpa only [Finset.coe_singleton] using
    (check_buchi_iff table {1} 1000 0 (by decide +kernel)).mp some_recurrent_path

end Branching

namespace CoveredObservation

/-- Two distinct transitions form a cycle; the third state is isolated. -/
def original : ReductionSpan (Fin 3) where
  Edge := Bool
  source event := if event then 0 else 1
  target event := if event then 1 else 0

def observed : ReductionSpan (Fin 2) where
  Edge := Unit
  source _ := 0
  target _ := 0

def observation : SpanMap original observed where
  states state := if state = 2 then 1 else 0
  events _ := ()
  source_comm := by unfold original observed; decide +kernel
  target_comm := by unfold original observed; decide +kernel

theorem outgoing_coverage : observation.SourceLifts := by
  unfold SpanMap.SourceLifts observation original observed
  decide +kernel
theorem incoming_coverage : observation.TargetLifts := by
  unfold SpanMap.TargetLifts observation original observed
  decide +kernel

theorem actually_identifies_states : observation.states 0 = observation.states 1 ∧ (0 : Fin 3) ≠ 1 := by
  decide +kernel

theorem accepting_preimage : observation.states ⁻¹' ({0} : Set (Fin 2)) = ({0, 1} : Set (Fin 3)) := by
  ext state
  change (if state = 2 then (1 : Fin 2) else 0) = 0 ↔ state = 0 ∨ state = 1
  fin_cases state <;> decide

def table : FiniteGraph.Table observed where
  edge source target := decide (source = 0 ∧ target = 0)
  exact := by unfold observed; decide +kernel

def accepting : FiniteMuCalculus.Environment (Fin 2) 1 := fun _ => {0}

theorem coverage : CoversFormula observation (Formula.buchi .future) :=
  buchi_coverage observation outgoing_coverage

theorem source_zero_proved :
    ((checkSource table observation (Formula.buchi .future) coverage accepting 1000 0).map Outcome.answer) =
      some (some true) := by decide +kernel

theorem source_one_proved :
    ((checkSource table observation (Formula.buchi .future) coverage accepting 1000 1).map Outcome.answer) =
      some (some true) := by decide +kernel

theorem source_isolated_refuted :
    ((checkSource table observation (Formula.buchi .future) coverage accepting 1000 2).map Outcome.answer) =
      some (some false) := by decide +kernel

theorem source_budget_unknown :
    ((checkSource table observation (Formula.buchi .future) coverage accepting 0 0).map Outcome.answer) =
      some none := by decide +kernel

theorem past_coverage : CoversFormula observation (.box .past (.ff : Formula Traversal 0)) :=
  ⟨incoming_coverage, trivial⟩

theorem source_incoming_cycle_refuted :
    ((checkSource table observation (.box .past .ff) past_coverage (fun index : Fin 0 => index.elim0)
      10 0).map Outcome.answer) = some (some false) := by decide +kernel

theorem source_incoming_isolated_proved :
    ((checkSource table observation (.box .past .ff) past_coverage (fun index : Fin 0 => index.elim0)
      10 2).map Outcome.answer) = some (some true) := by decide +kernel

theorem source_query_exact (source : Fin 3) :
    ((checkSource table observation (Formula.buchi .future) coverage accepting 1000 source).map Outcome.answer) =
        some (some true) ↔
      satisfies (transitionSystem original)
        (pullEnvironment observation.states accepting.meaning) (Formula.buchi .future) source :=
  checkSource_positive_iff table observation _ coverage (Formula.buchi_positive _) accepting 1000 source
    (by decide +kernel)

theorem source_semantic_positive :
    satisfies (transitionSystem original)
      (pullEnvironment observation.states accepting.meaning) (Formula.buchi .future) 0 :=
  (source_query_exact 0).mp source_zero_proved

theorem source_semantic_negative :
    ¬ satisfies (transitionSystem original)
      (pullEnvironment observation.states accepting.meaning) (Formula.buchi .future) 2 := by
  intro satisfied
  have positive := (source_query_exact 2).mpr satisfied
  rw [source_isolated_refuted] at positive
  cases positive

end CoveredObservation

def run : IO Unit := do
  let checks := [
    ((check Directional.table (.box .past (.var 0)) Directional.observed 10 0).map Outcome.answer) == some (some false),
    ((check Directional.table (.box .future (.var 0)) Directional.observed 10 0).map Outcome.answer) == some (some true),
    ((check Directional.table (.box .future (.var 0)) Directional.observed 0 0).map Outcome.answer) == some none,
    ((check Directional.table (Formula.buchi .future) (fun _ => {1}) 1000 1).map Outcome.answer) == some (some false),
    ((check Directional.table (Formula.buchi .future) (fun _ => {1}) 1000 0).map Outcome.answer) == some (some false),
    ((check Directional.table (Formula.buchi .future) (fun _ => {0}) 1000 0).map Outcome.answer) == some (some true),
    (check Directional.table (.mu (.neg (.var 0))) (fun index : Fin 0 => index.elim0) 1000 0).isNone,
    ((check Branching.table (Formula.buchi .future) Branching.accepting 1000 0).map Outcome.answer) == some (some true),
    ((check Branching.table (.box .future (Formula.buchi .future)) Branching.accepting 1000 0).map Outcome.answer) == some (some false),
    ((check Branching.table (.diamond .future (.var 0)) Branching.accepting 10 0).map Outcome.answer) == some (some true),
    ((check Branching.table (.box .future (.var 0)) Branching.accepting 10 0).map Outcome.answer) == some (some false),
    ((checkSource CoveredObservation.table CoveredObservation.observation (Formula.buchi .future)
      CoveredObservation.coverage CoveredObservation.accepting 1000 0).map Outcome.answer) == some (some true),
    ((checkSource CoveredObservation.table CoveredObservation.observation (Formula.buchi .future)
      CoveredObservation.coverage CoveredObservation.accepting 1000 1).map Outcome.answer) == some (some true),
    ((checkSource CoveredObservation.table CoveredObservation.observation (Formula.buchi .future)
      CoveredObservation.coverage CoveredObservation.accepting 1000 2).map Outcome.answer) == some (some false),
    ((checkSource CoveredObservation.table CoveredObservation.observation (Formula.buchi .future)
      CoveredObservation.coverage CoveredObservation.accepting 0 0).map Outcome.answer) == some none,
    ((checkSource CoveredObservation.table CoveredObservation.observation (.box .past .ff)
      CoveredObservation.past_coverage (fun index : Fin 0 => index.elim0) 10 0).map Outcome.answer) == some (some false),
    ((checkSource CoveredObservation.table CoveredObservation.observation (.box .past .ff)
      CoveredObservation.past_coverage (fun index : Fin 0 => index.elim0) 10 2).map Outcome.answer) == some (some true)]
  if !checks.all id then throw (IO.userError "Public finite native-query control failed")
  IO.println s!"Public finite native-query controls: {checks.length} passed"

#eval run

end Mettapedia.OSLF.NativeTypes.Executable.Finite.Controls
