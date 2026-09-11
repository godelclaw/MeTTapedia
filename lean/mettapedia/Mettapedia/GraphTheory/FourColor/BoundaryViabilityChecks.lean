import Mettapedia.GraphTheory.FourColor.BoundarySmallCutViability
import Mettapedia.GraphTheory.FourColor.BoundarySmallCutChecks

/-! # Kernel controls for boundary visibility and connectivity

The rejection predicate concerns future vertices. It must distinguish
the empty initial object, a live open piece, an invisible isolated
vertex, and a valid closed final object. No colouring data is enumerated.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryViabilityChecks

open GoertzelV24BoundaryEssentialGluing BoundarySmallCutExecutable
open BoundarySmallCutViability BoundarySmallCutChecks

def noPorts : Fin 0 → Fin 2 := Fin.elim0

def empty : Multigraph (Fin 0) (Fin 0) := ⟨Fin.elim0, Fin.elim0⟩

theorem empty_initial_live : rejectsExtension (extract empty id) = false := by decide +kernel

theorem open_connected_live :
    rejectsExtension (extract (parallel 2) id) = false := by decide +kernel

theorem invisible_vertex_detected :
    rejectsExtension (extract (parallel 0) (fun _ : Fin 1 => (0 : Fin 2))) = true := by
  decide +kernel

theorem closed_no_extension :
    rejectsExtension (extract (parallel 2) noPorts) = true := by decide +kernel

theorem closed_final_accepted :
    accepts (extract (parallel 2) noPorts) = true := by decide +kernel

theorem ports_joined : sameComponent (extract (parallel 1) id) 0 1 = true := by decide +kernel

theorem ports_separate : sameComponent (extract (parallel 0) id) 0 1 = false := by decide +kernel

theorem actual_tangle_live : rejectsExtension (extractTangle edgeTangle) = false := by
  decide +kernel

theorem actual_tangle_connected :
    sameComponent (extractTangle edgeTangle) (.inl 0) (.inr 0) = true := by decide +kernel

/-- The computed closed record triggers the generic no-completion theorem. -/
theorem closed_cannot_acquire_exterior :
    ¬ (glue (parallel 2) (parallel 1) noPorts noPorts).Connected := by
  apply hidden_no_connected_glue (parallel 2) noPorts (parallel 1) noPorts
  rw [← extract_correct]
  exact (rejectsExtension_iff _).mp closed_no_extension

end Mettapedia.GraphTheory.FourColor.BoundaryViabilityChecks
