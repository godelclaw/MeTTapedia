import Mettapedia.Analysis.EuclideanCrossProduct
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! # Joint smoothness of the Euclidean cross product -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanCrossProduct

open scoped ContDiff

local notation "E3" => EuclideanSpace ℝ (Fin 3)

@[fun_prop] theorem contDiff_cross :
    ContDiff ℝ ∞ (fun p : E3 × E3 ↦ cross p.1 p.2) := by
  apply (contDiff_piLp 2).2
  intro i
  fin_cases i <;> simp only [cross, cross_apply, WithLp.ofLp_toLp] <;> dsimp <;> fun_prop

end Mettapedia.Analysis.EuclideanCrossProduct
