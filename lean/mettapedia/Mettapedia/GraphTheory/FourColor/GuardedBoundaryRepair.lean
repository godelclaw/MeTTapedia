import Mettapedia.GraphTheory.Kempe.GuardedLift
import Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction

/-!
# Guarded elimination rejects the obstruction and preserves its repair

The same interacting hidden pair has a blocked fixed-context command and
a successful repair with one boundary vertex temporarily available. The
joint transition guard distinguishes them without a history table.
-/

namespace Mettapedia.GraphTheory.FourColor.GuardedBoundaryRepair

open SimpleGraph Relation AdjacentHiddenObstruction

private theorem boundary_retained : boundary ⊆ ({0, 1} : Set (Fin 9))ᶜ := by
  change ∀ v : Fin 9, 3 ≤ v.val → ¬ (v = 0 ∨ v = 1)
  decide +kernel

/-- Endpoint extension does not bypass the transition guard. -/
theorem blocked_step :
    ¬ KempeGuardedLift.Step ({0, 1} : Set (Fin 9)) boundary
      ((state 0).restrictInduce ({0, 1} : Set (Fin 9))ᶜ)
      ((state 3).restrictInduce ({0, 1} : Set (Fin 9))ᶜ) := by
  intro step
  exact no_lift (state 3) rfl
    (KempeGuardedLift.lift {0, 1} boundary boundary_retained
      (KempeGuardedLift.two_vertex_fibres 0 1) (state 0) (state 3) step)

/-- No chain of guarded commands can silently evade the physical obstruction. -/
theorem blocked_history :
    ¬ ReflTransGen (KempeGuardedLift.Step ({0, 1} : Set (Fin 9)) boundary)
      ((state 0).restrictInduce ({0, 1} : Set (Fin 9))ᶜ)
      ((state 3).restrictInduce ({0, 1} : Set (Fin 9))ᶜ) := by
  intro path
  exact no_lift (state 3) rfl
    ((KempeGuardedLift.two_vertex_history_iff 0 1 boundary boundary_retained
      (state 0) (state 3)).mp path)

/-- The existing three-switch repair survives the same guarded interface
when the permitted context includes the cooperating boundary leaf. -/
theorem repaired_guarded_history :
    ReflTransGen (KempeGuardedLift.Step ({0, 1} : Set (Fin 9)) fixedContext)
      ((state 0).restrictInduce ({0, 1} : Set (Fin 9))ᶜ)
      ((state 3).restrictInduce ({0, 1} : Set (Fin 9))ᶜ) :=
  (KempeGuardedLift.projects {0, 1} fixedContext).reach repaired

end Mettapedia.GraphTheory.FourColor.GuardedBoundaryRepair
