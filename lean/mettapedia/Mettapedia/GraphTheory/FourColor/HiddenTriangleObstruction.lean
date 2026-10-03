import Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction
import Mettapedia.GraphTheory.Kempe.GuardedLift

/-!
# Three interacting hidden vertices can lose a reachable-state distinction

Hide the complete core triangle of the nine-vertex obstruction. Two proper
colourings now have the same retained state, but no history between them
fixes that state. Even exact before/after step guards cannot recover a hidden
distinction erased from the states themselves. This limits extension of the
pair theorem to arbitrary larger blocks. The witness has pendant vertices;
no minimal-counterexample geometry is claimed.
-/

namespace Mettapedia.GraphTheory.FourColor.HiddenTriangleObstruction

open SimpleGraph Relation AdjacentHiddenObstruction

def hidden : Set (Fin 9) := {0, 1, 2}

theorem retained_eq : hiddenᶜ = boundary := by
  ext v
  change (¬ (v = 0 ∨ v = 1 ∨ v = 2)) ↔ 3 ≤ v.val
  fin_cases v <;> decide +kernel

/-- A projection to the retained colouring identifies the two states. -/
theorem same_retained :
    (state 0).restrictInduce hiddenᶜ = (state 3).restrictInduce hiddenᶜ := by
  apply Coloring.restrictInduce_eq_iff.mpr
  apply Coloring.boundaryWord_eq_iff.mpr
  intro v hv
  exact same_boundary v (retained_eq ▸ hv)

/-- Automatic fibre connectivity for hidden pairs does not extend to an
arbitrary block of three vertices, even a triangle. -/
theorem not_fibres : ¬ graph.FibreConnected (Fin 4) hiddenᶜ := by
  intro h
  have path := h (state 0) (state 3) (Coloring.restrictInduce_eq_iff.mp same_retained)
  rw [retained_eq] at path
  exact no_lift (state 3) rfl path

/-- No restriction of the step relation alone can distinguish these identical
retained states: their reflexive path already fails to lift. -/
theorem guarded_stutter_does_not_lift :
    ReflTransGen (KempeGuardedLift.Step hidden boundary)
      ((state 0).restrictInduce hiddenᶜ) ((state 3).restrictInduce hiddenᶜ) ∧
    ¬ ReflTransGen (graph.KempeStepAvoiding boundary) (state 0) (state 3) := by
  refine ⟨?_, no_lift (state 3) rfl⟩
  rw [same_retained]

end Mettapedia.GraphTheory.FourColor.HiddenTriangleObstruction
