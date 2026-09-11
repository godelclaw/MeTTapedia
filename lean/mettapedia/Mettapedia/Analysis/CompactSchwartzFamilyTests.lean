import Mettapedia.Analysis.CompactSchwartzFamily
import Mettapedia.Analysis.SmoothAnnulus

/-! Boundary and parameter-family regressions for annular Fourier localization. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.CompactSchwartzFamilyTests

open MeasureTheory SmoothAnnulus CompactSchwartzFamily
open scoped ContDiff FourierTransform SchwartzMap

example : denominator (0 : ℝ) = 1 := by simp [denominator, buffer_zero]

example : cutoff (1 : ℝ) = 1 ∧ cutoff (2 : ℝ) = 1 := by
  constructor <;> apply cutoff_eq_one <;> norm_num

example : cutoff (4 : ℝ) = 0 := by
  by_contra hn
  have h := (norm_bounds_of_cutoff_ne_zero (4 : ℝ) hn).2
  norm_num at h

/-- The compact-parameter theorem handles varying amplitudes, not just a fixed symbol. -/
example {d : ℕ} (s : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (hc : HasCompactSupport (s : EuclideanSpace ℝ (Fin d) → ℂ)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ m * ‖(𝓕⁻ (t • s)) x‖) ≤ C := by
  apply exists_uniform_fourierInv_moment (fun t : ℝ ↦ t • s) _ _ isCompact_Icc
    (tsupport s) hc _ m
  · exact contDiff_fst.smul ((s.smooth ⊤).comp contDiff_snd)
  · intro t
    apply closure_minimal _ (isClosed_tsupport s)
    intro x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp [hz])

end Mettapedia.Analysis.CompactSchwartzFamilyTests

#print axioms Mettapedia.Analysis.CompactSchwartzFamily.norm_iteratedFDeriv_section_le
#print axioms Mettapedia.Analysis.CompactSchwartzFamily.exists_uniform_weighted_derivative_bound
#print axioms Mettapedia.Analysis.CompactSchwartzFamily.exists_uniform_seminorm_bound
#print axioms Mettapedia.Analysis.CompactSchwartzFamily.exists_uniform_derivative_integral_bound
#print axioms Mettapedia.Analysis.CompactSchwartzFamily.pow_mul_norm_fourierInv_le
#print axioms Mettapedia.Analysis.CompactSchwartzFamily.exists_uniform_fourierInv_decay
#print axioms Mettapedia.Analysis.CompactSchwartzFamily.exists_uniform_fourierInv_moment
#print axioms Mettapedia.Analysis.SmoothAnnulus.cutoff_nonneg
#print axioms Mettapedia.Analysis.SmoothAnnulus.cutoff_le_one
#print axioms Mettapedia.Analysis.SmoothAnnulus.buffer_nonneg
#print axioms Mettapedia.Analysis.SmoothAnnulus.buffer_le_one
#print axioms Mettapedia.Analysis.SmoothAnnulus.norm_bounds_of_cutoff_ne_zero
#print axioms Mettapedia.Analysis.SmoothAnnulus.norm_bounds_of_buffer_ne_zero
#print axioms Mettapedia.Analysis.SmoothAnnulus.buffer_eq_one_of_cutoff_ne_zero
#print axioms Mettapedia.Analysis.SmoothAnnulus.cutoff_eq_one
#print axioms Mettapedia.Analysis.SmoothAnnulus.buffer_zero
#print axioms Mettapedia.Analysis.SmoothAnnulus.denominator_pos
#print axioms Mettapedia.Analysis.SmoothAnnulus.denominator_eq_norm_sq
#print axioms Mettapedia.Analysis.SmoothAnnulus.contDiff_cutoff
#print axioms Mettapedia.Analysis.SmoothAnnulus.contDiff_buffer
#print axioms Mettapedia.Analysis.SmoothAnnulus.hasCompactSupport_cutoff
#print axioms Mettapedia.Analysis.SmoothAnnulus.tsupport_cutoff_subset
