import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Positive cosine powers and the Beta integral

The substitution `u = sin(t)²` is performed on the open quadrant, where its
derivative and all power cancellations are justified. Endpoints are removed
only by null-set agreement. The result gives the integral needed for uniform
complex-phase moments without defining those moments by a Gamma expression.
-/

namespace Mettapedia.Analysis

open Real Set MeasureTheory
open scoped Interval

noncomputable section

/-- The real Beta kernel integrates to the standard Beta normalizer. -/
theorem integral_betaKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ u in Ioo (0 : ℝ) 1, u ^ (a - 1) * (1 - u) ^ (b - 1)) =
      ProbabilityTheory.beta a b := by
  apply Complex.ofReal_injective
  have hcast := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun u => u ^ (a - 1) * (1 - u) ^ (b - 1))
  refine hcast.symm.trans ?_
  have hbeta : (ProbabilityTheory.beta a b : ℂ) = Complex.betaIntegral a b := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
    simp [ProbabilityTheory.beta, ← Complex.Gamma_ofReal]
  rw [hbeta, Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  change Complex.ofReal (u ^ (a - 1) * (1 - u) ^ (b - 1)) = _
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hu.1.le,
    Complex.ofReal_cpow (sub_nonneg.2 hu.2.le)]
  push_cast
  rfl

/-- The Beta change of variables, with endpoint values handled by null sets. -/
theorem two_mul_integral_cos_rpow_eq_beta {p : ℝ} (hp : 0 < p) :
    2 * (∫ t in (0 : ℝ)..π / 2, cos t ^ p) =
      ProbabilityTheory.beta (1 / 2) ((p + 1) / 2) := by
  let kernel (u : ℝ) := u ^ ((1 : ℝ) / 2 - 1) * (1 - u) ^ ((p + 1) / 2 - 1)
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => sin t ^ 2) (2 * sin t * cos t) t := by
    convert! (Real.hasDerivAt_sin t).pow 2 using 1
    norm_num
  have hnonneg (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (π / 2)) : 0 ≤ 2 * sin t * cos t := by
    have hs := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
    have hc := cos_pos_of_mem_Ioo (show t ∈ Ioo (-(π / 2)) (π / 2) from
      ⟨by linarith [ht.1, pi_pos], ht.2⟩)
    positivity
  have hchange := integral_Icc_deriv_smul_of_deriv_nonneg
    (f := fun t : ℝ => sin t ^ 2) (f' := fun t => 2 * sin t * cos t)
    (g := kernel) (continuous_sin.pow 2).continuousOn (fun t _ => hd t)
    hnonneg (by positivity : (0 : ℝ) ≤ π / 2)
  simp only [sin_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sin_pi_div_two, one_pow,
    smul_eq_mul, integral_Icc_eq_integral_Ioo] at hchange
  have hkernel (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (π / 2)) :
      (2 * sin t * cos t) * kernel (sin t ^ 2) = 2 * cos t ^ p := by
    have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
    have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
    have hsq : 1 - sin t ^ 2 = cos t ^ 2 := by nlinarith [sin_sq_add_cos_sq t]
    dsimp [kernel]
    rw [hsq, ← Real.rpow_natCast (sin t) 2, ← Real.rpow_mul hs.le,
      ← Real.rpow_natCast (cos t) 2, ← Real.rpow_mul hc.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * ((p + 1) / 2 - 1) = p - 1 by ring,
      Real.rpow_neg_one, Real.rpow_sub hc, Real.rpow_one]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hkernel] at hchange
  rw [integral_const_mul, integral_betaKernel (by norm_num) (by linarith)] at hchange
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2),
    integral_Ioc_eq_integral_Ioo]
  exact hchange

/-- A Gamma evaluation of every positive real cosine power. -/
theorem integral_cos_rpow {p : ℝ} (hp : 0 < p) :
    (∫ t in (0 : ℝ)..π / 2, cos t ^ p) =
      √π * Gamma ((p + 1) / 2) / (2 * Gamma (p / 2 + 1)) := by
  have h := two_mul_integral_cos_rpow_eq_beta hp
  rw [ProbabilityTheory.beta, Real.Gamma_one_half_eq,
    show (1 : ℝ) / 2 + (p + 1) / 2 = p / 2 + 1 by ring] at h
  have hg : 0 < Gamma (p / 2 + 1) := Gamma_pos_of_pos (by linarith)
  rw [eq_div_iff (by positivity : 2 * Gamma (p / 2 + 1) ≠ 0)]
  have h' := (eq_div_iff hg.ne').1 h
  nlinarith [h']

/-- The scaled cosine moment in the central Gamma-ratio form. -/
theorem scaled_integral_cos_rpow_eq_gamma {p : ℝ} (hp : 0 < p) :
    (2 : ℝ) ^ (p + 1) / π * (∫ t in (0 : ℝ)..π / 2, cos t ^ p) =
      Gamma (p + 1) / Gamma (p / 2 + 1) ^ 2 := by
  rw [integral_cos_rpow hp]
  have hg : Gamma (p / 2 + 1) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  have hs : (√π) ^ 2 = π := Real.sq_sqrt pi_pos.le
  have hd := Gamma_mul_Gamma_add_half ((p + 1) / 2)
  rw [show (p + 1) / 2 + 1 / 2 = p / 2 + 1 by ring,
    show 2 * ((p + 1) / 2) = p + 1 by ring,
    show 1 - (p + 1) = -p by ring] at hd
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  field_simp [hg, pi_ne_zero]
  have hp2 : (2 : ℝ) ^ p ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) p).ne'
  have heq := congrArg (fun r : ℝ => (2 : ℝ) ^ p * √π * r) hd
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at heq
  field_simp [hp2] at heq
  nlinarith only [congrArg (fun r : ℝ => √π * r) heq,
    congrArg (fun r : ℝ => r * Gamma (p + 1)) hs]

end

end Mettapedia.Analysis
