import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.DerivativeTest

/-! Local second-derivative linearity and the sign at a continuous local minimum. -/

set_option autoImplicit false
open scoped Topology ContDiff

namespace Mettapedia.Analysis

theorem deriv_deriv_linearCombination {f g : ℝ → ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f t) (hg : ContDiffAt ℝ 2 g t) (a b : ℝ) :
    deriv (deriv (fun τ ↦ a * f τ + b * g τ)) t =
      a * deriv (deriv f) t + b * deriv (deriv g) t := by
  have he : deriv (fun τ ↦ a * f τ + b * g τ) =ᶠ[𝓝 t]
      (fun τ ↦ a * deriv f τ + b * deriv g τ) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with τ hfτ hgτ
    exact (((hfτ.differentiableAt (by norm_num)).hasDerivAt.const_mul a).add
      ((hgτ.differentiableAt (by norm_num)).hasDerivAt.const_mul b)).deriv
  rw [he.deriv_eq]
  exact (((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt.const_mul a |>.add
    (((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt.const_mul b)).deriv

theorem deriv_deriv_smul_const_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ} {g : ℝ → E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f t) (hg : ContDiffAt ℝ 2 g t) (v : E) :
    deriv (deriv (fun τ ↦ f τ • v - g τ)) t =
      deriv (deriv f) t • v - deriv (deriv g) t := by
  have he : deriv (fun τ ↦ f τ • v - g τ) =ᶠ[𝓝 t]
      (fun τ ↦ deriv f τ • v - deriv g τ) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with τ hfτ hgτ
    exact (((hfτ.differentiableAt (by norm_num)).hasDerivAt.smul_const v).sub
      (hgτ.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [he.deriv_eq]
  exact ((((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt.smul_const v).sub
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt).deriv

/-- A continuous local minimum cannot have a negative second derivative.
No separate existence hypothesis is needed for Lean's total derivative. -/
theorem second_derivative_nonneg_of_isLocalMin {f : ℝ → ℝ} {t : ℝ}
    (hmin : IsLocalMin f t) (hc : ContinuousAt f t) : 0 ≤ deriv (deriv f) t := by
  by_contra hn
  have hneg := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 t] (fun _ ↦ f t) :=
    (hmin.and hmax).mono (fun _ h ↦ le_antisymm h.2 h.1)
  have hz := he.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hz
  linarith

end Mettapedia.Analysis
