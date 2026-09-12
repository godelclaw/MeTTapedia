import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # A signed time-weighted identity for absolutely continuous functions -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AbsolutelyContinuousTimeWeight

open Filter MeasureTheory

theorem integral_eq_initial_add_weighted_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (∫ t in a..b, f t) = (b - a) * f a + ∫ t in a..b, (b - t) * deriv f t := by
  have hg : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ b - t) a b :=
    ((contDiff_const.sub contDiff_id : ContDiff ℝ 1 (fun t : ℝ ↦ b - t)).contDiffOn).absolutelyContinuousOnInterval
  have hd (t : ℝ) : deriv (fun τ : ℝ ↦ b - τ) t = -1 :=
    ((hasDerivAt_id t).const_sub b).deriv
  have h := hg.integral_mul_deriv_eq_deriv_mul hf
  simp only [sub_self, zero_mul, hd, neg_one_mul, intervalIntegral.integral_neg] at h
  linarith

theorem integral_eq_initial_add_weighted_rate {f r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ Set.Ioo a b → HasDerivAt f (r t) t) :
    IntervalIntegrable (fun t ↦ (b - t) * r t) volume a b ∧
      (∫ t in a..b, f t) = (b - a) * f a + ∫ t in a..b, (b - t) * r t := by
  have heq : deriv f =ᵐ[volume.restrict (Set.uIoc a b)] r := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [hd, (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t hdt he hmem
    have hm : t ∈ Set.Icc a b := by
      simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hmem
    exact (hdt (he.mpr hm)).deriv
  have hw : (fun t ↦ (b - t) * deriv f t) =ᵐ[volume.restrict (Set.uIoc a b)]
      (fun t ↦ (b - t) * r t) := heq.mono (fun t h ↦ congrArg (fun v ↦ (b - t) * v) h)
  refine ⟨(hf.intervalIntegrable_deriv.continuousOn_mul (by fun_prop)).congr_ae hw, ?_⟩
  rw [integral_eq_initial_add_weighted_deriv hf, intervalIntegral.integral_congr_ae_restrict hw]

end Mettapedia.Analysis.AbsolutelyContinuousTimeWeight
