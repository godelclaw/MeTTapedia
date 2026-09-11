import Mettapedia.Analysis.SchwartzDilation
import Mettapedia.Analysis.SmoothAnnulus

/-! Jacobian, orientation, and spatial-moment regressions for kernel dilation. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SchwartzLinearChangeTests

open MeasureTheory SchwartzLinearChange SchwartzDilation
open scoped FourierTransform SchwartzMap

local notation "E6" => EuclideanSpace ℝ (Fin 6)

/-- Six spatial coordinates contribute six Jacobian powers, regardless of orientation. -/
example (s : 𝓢(E6, ℂ)) (x : E6) :
    dilate (-2) (by norm_num) s x = (64 : ℝ) • s ((-2 : ℝ) • x) := by
  norm_num [dilate_apply, finrank_euclideanSpace]

/-- Doubling frequency halves the first spatial moment, not its mass. -/
example (s : 𝓢(E6, ℂ)) :
    (∫ x : E6, ‖dilate 2 (by norm_num) s x‖) = ∫ x : E6, ‖s x‖ :=
  mass_dilate 2 (by norm_num) s

example (s : 𝓢(E6, ℂ)) :
    (∫ x : E6, ‖x‖ * ‖dilate 2 (by norm_num) s x‖) =
      (1 / 2 : ℝ) * ∫ x : E6, ‖x‖ * ‖s x‖ := by
  simpa using moment_dilate 2 (by norm_num) s 1

/-- Reflection changes the Fourier argument, without a spurious minus sign on the kernel density. -/
example (s : 𝓢(E6, ℂ)) (ξ : E6) :
    (𝓕 (dilate (-1) (by norm_num) s)) ξ = (𝓕 s) (-ξ) := by
  simpa using fourier_dilate (-1) (by norm_num) s ξ

end Mettapedia.Analysis.SchwartzLinearChangeTests

#print axioms Mettapedia.Analysis.SchwartzDilation.dilationEquiv_apply
#print axioms Mettapedia.Analysis.SchwartzDilation.dilationEquiv_symm_apply
#print axioms Mettapedia.Analysis.SchwartzDilation.jacobian_dilationEquiv
#print axioms Mettapedia.Analysis.SchwartzDilation.dilate_apply
#print axioms Mettapedia.Analysis.SchwartzDilation.inverse_adjoint_dilationEquiv
#print axioms Mettapedia.Analysis.SchwartzDilation.fourier_dilate
#print axioms Mettapedia.Analysis.SchwartzDilation.moment_dilate
#print axioms Mettapedia.Analysis.SchwartzDilation.mass_dilate
#print axioms Mettapedia.Analysis.SchwartzLinearChange.jacobian_pos
#print axioms Mettapedia.Analysis.SchwartzLinearChange.integral_comp_linearEquiv
#print axioms Mettapedia.Analysis.SchwartzLinearChange.pullback_apply
#print axioms Mettapedia.Analysis.SchwartzLinearChange.integral_jacobian_comp
#print axioms Mettapedia.Analysis.SchwartzLinearChange.fourier_pullback
#print axioms Mettapedia.Analysis.SchwartzLinearChange.moment_pullback
#print axioms Mettapedia.Analysis.SchwartzLinearChange.mass_pullback
#print axioms Mettapedia.Analysis.SchwartzLinearChange.moment_pullback_le
#print axioms Mettapedia.Analysis.SmoothAnnulus.cutoff_zero
