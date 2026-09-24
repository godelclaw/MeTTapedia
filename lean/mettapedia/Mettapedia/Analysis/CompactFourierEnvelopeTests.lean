import Mettapedia.Analysis.CompactFourierEnvelope
import Mettapedia.Analysis.DensityLinearChange
import Mettapedia.Analysis.SchwartzDilation

/-! Exact tail values, nontrivial dilation, and integrable moment regressions. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.CompactFourierEnvelopeTests

open MeasureTheory CompactFourierEnvelope DensityLinearChange SchwartzDilation SchwartzLinearChange
open scoped SchwartzMap FourierTransform ContDiff

example : polynomialTail 2 (3 : ℝ) = 1 / 16 := by
  norm_num [polynomialTail, Real.rpow_neg, Real.rpow_natCast]

example : polynomialTail 7 (0 : ℝ) = 1 := by simp [polynomialTail]

example : pullbackDensity (dilationEquiv (E := ℝ) 2 (by norm_num)) (polynomialTail 2) 1 = 2 / 9 := by
  norm_num [pullbackDensity, jacobian_dilationEquiv, polynomialTail,
    Real.rpow_neg, Real.rpow_natCast]

example : Integrable (fun x : ℝ ↦ ‖x‖ * polynomialTail (1 + (volume : Measure ℝ).integrablePower) x) := by
  simpa only [pow_one] using integrable_moment_polynomialTail (volume : Measure ℝ) 1

/-- Dilation retains the exact mass of a nonnegative tail. -/
example : (∫ x : ℝ, pullbackDensity (dilationEquiv 2 (by norm_num))
    (polynomialTail (1 + (volume : Measure ℝ).integrablePower)) x) =
      ∫ x : ℝ, polynomialTail (1 + (volume : Measure ℝ).integrablePower) x :=
  integral_pullbackDensity _ _

/-- A varying real amplitude has one majorant for every parameter in the interval. -/
example {d : ℕ} (s : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (hc : HasCompactSupport (s : EuclideanSpace ℝ (Fin d) → ℂ)) (m : ℕ) :
    ∃ H : EuclideanSpace ℝ (Fin d) → ℝ, (∀ x, 0 ≤ H x) ∧ Continuous H ∧ Integrable H ∧
      Integrable (fun x ↦ ‖x‖ ^ m * H x) ∧
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ x, ‖(𝓕⁻ (t • s)) x‖ ≤ H x := by
  apply exists_uniform_fourierInv_envelope (fun t : ℝ ↦ t • s) _ _ isCompact_Icc
    (tsupport s) hc _ m
  · exact contDiff_fst.smul ((s.smooth ⊤).comp contDiff_snd)
  · intro t
    apply closure_minimal _ (isClosed_tsupport s)
    intro x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp [hz])

end Mettapedia.Analysis.CompactFourierEnvelopeTests

#print axioms Mettapedia.Analysis.CompactFourierEnvelope.polynomialTail_nonneg
#print axioms Mettapedia.Analysis.CompactFourierEnvelope.continuous_polynomialTail
#print axioms Mettapedia.Analysis.CompactFourierEnvelope.pow_mul_polynomialTail_le
#print axioms Mettapedia.Analysis.CompactFourierEnvelope.polynomialTail_add_le
#print axioms Mettapedia.Analysis.CompactFourierEnvelope.integrable_moment_polynomialTail
#print axioms Mettapedia.Analysis.CompactFourierEnvelope.integrable_polynomialTail_add
#print axioms Mettapedia.Analysis.CompactFourierEnvelope.exists_uniform_fourierInv_envelope
#print axioms Mettapedia.Analysis.DensityLinearChange.pullbackDensity_nonneg
#print axioms Mettapedia.Analysis.DensityLinearChange.continuous_pullbackDensity
#print axioms Mettapedia.Analysis.DensityLinearChange.integrable_pullbackDensity
#print axioms Mettapedia.Analysis.DensityLinearChange.integral_pullbackDensity
#print axioms Mettapedia.Analysis.DensityLinearChange.integral_moment_pullbackDensity
#print axioms Mettapedia.Analysis.DensityLinearChange.integrable_moment_pullbackDensity
#print axioms Mettapedia.Analysis.DensityLinearChange.integral_moment_pullbackDensity_le
