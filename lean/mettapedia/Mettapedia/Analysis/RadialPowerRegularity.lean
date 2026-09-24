import Mettapedia.Analysis.RadialPower
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Smoothness of even radial powers, including at the origin -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialPower

open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_radialPower_even (n : ℕ) :
    ContDiff ℝ ∞ (radialPower (2 * n) : E → E) := by
  have he : (radialPower (2 * n) : E → E) = (fun x ↦ (‖x‖ ^ 2) ^ n • x) := by
    funext x
    simp only [radialPower, pow_mul]
  rw [he]
  exact ((contDiff_norm_sq (𝕜 := ℝ) : ContDiff ℝ ∞ (fun x : E ↦ ‖x‖ ^ 2)).pow n).smul
    contDiff_id

end Mettapedia.Analysis.RadialPower
