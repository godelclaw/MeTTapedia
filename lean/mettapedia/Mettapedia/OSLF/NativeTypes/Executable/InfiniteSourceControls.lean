import Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter

/-!
# An unbounded counter checked through its finite parity observation

The source has one transition from each natural number to its successor.
Its two-state parity observation has exact outgoing coverage but lacks incoming
coverage at zero. The finite checker decides recurrence of even states, and
path transport supplies an actual infinite recurrent source execution.

This is a covered finite observation of an infinite source, not a construction
of a material-state quotient or a bounded exploration of the source.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Finite.InfiniteSourceControls

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.BuchiTransport
open Reference.Core (Outcome)
open Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter

theorem acceptance_is_nonconstant :
    observation.states 0 ∈ ({0} : Set (Fin 2)) ∧
      observation.states 1 ∉ ({0} : Set (Fin 2)) := by
  decide +kernel

theorem even_start_proved :
    ((checkSource table observation (Formula.buchi .future) coverage accepting 1000 0).map Outcome.answer) =
      some (some true) := by decide +kernel

theorem odd_start_proved :
    ((checkSource table observation (Formula.buchi .future) coverage accepting 1000 1).map Outcome.answer) =
      some (some true) := by decide +kernel

theorem empty_acceptance_refuted :
    ((checkSource table observation (Formula.buchi .future) coverage (fun _ => ∅) 1000 0).map Outcome.answer) =
      some (some false) := by decide +kernel

theorem insufficient_allowance_unknown :
    ((checkSource table observation (Formula.buchi .future) coverage accepting 0 0).map Outcome.answer) =
      some none := by decide +kernel

theorem every_observed_start_proved :
    ∀ state : Fin 2,
      ((check table (Formula.buchi .future) accepting 1000 state).map Outcome.answer) =
        some (some true) := by decide +kernel

/-- The positive observation lifts to an actual unbounded source path. -/
theorem recurrent_counter_path (start : Nat) :
    BuchiPath (transitionSystem counter) .future {index | index % 2 = 0} start := by
  have observedPath : BuchiPath (transitionSystem parity) .future
      ({0} : Set (Fin 2)) (observation.states start) := by
    simpa only [Finset.coe_singleton] using
      (check_buchi_iff table {0} 1000 (observation.states start) (by decide +kernel)).mp
        (every_observed_start_proved (observation.states start))
  rw [← accepting_preimage]
  exact path_lifted observation outgoing_coverage {0} start observedPath

/-- The source has no incoming transition at zero. Its parity observation
does, so this past-box property cannot be transported back by outgoing coverage. -/
theorem source_zero_has_no_predecessor :
    satisfies (transitionSystem counter) (fun index : Fin 0 => index.elim0)
      (.box .past .ff) 0 := by
  intro source incoming
  obtain ⟨event, ends, _⟩ := incoming
  simp [counter] at ends

theorem observed_zero_has_predecessor :
    ¬ satisfies (transitionSystem parity) (fun index : Fin 0 => index.elim0)
      (.box .past .ff) 0 := by
  intro claimed
  exact claimed 1 ⟨(1 : Fin 2), by decide +kernel, rfl⟩

def run : IO Unit := do
  let checks := [
    ((checkSource table observation (Formula.buchi .future) coverage accepting 1000 0).map Outcome.answer) == some (some true),
    ((checkSource table observation (Formula.buchi .future) coverage accepting 1000 1).map Outcome.answer) == some (some true),
    ((checkSource table observation (Formula.buchi .future) coverage accepting 1000 1000000).map Outcome.answer) == some (some true),
    ((checkSource table observation (Formula.buchi .future) coverage (fun _ => ∅) 1000 0).map Outcome.answer) == some (some false),
    ((checkSource table observation (Formula.buchi .future) coverage accepting 0 0).map Outcome.answer) == some none,
    ((check table (.box .past (.ff : Formula Traversal 0))
      (fun index : Fin 0 => index.elim0) 10 0).map Outcome.answer) == some (some false)]
  if !checks.all id then throw (IO.userError "Infinite-source native-query control failed")
  IO.println s!"Infinite-source native-query controls: {checks.length} passed"

#eval run

end Mettapedia.OSLF.NativeTypes.Executable.Finite.InfiniteSourceControls
