import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.DerivativeTest

/-! Local second-derivative linearity and the sign at a continuous local minimum. -/

set_option autoImplicit false
open scoped Topology ContDiff

namespace Mettapedia.Analysis

/-- A local second-order power chain rule, with the exponent indexed so
that neither term uses a negative power. -/
theorem deriv_deriv_fun_pow_add_two {f : ℝ → ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f t) (n : ℕ) :
    deriv (deriv (fun s ↦ f s ^ (n + 2))) t =
      (n + 2 : ℝ) * (n + 1 : ℝ) * f t ^ n * deriv f t ^ 2 +
        (n + 2 : ℝ) * f t ^ (n + 1) * deriv (deriv f) t := by
  have he : deriv (fun s ↦ f s ^ (n + 2)) =ᶠ[𝓝 t]
      (fun s ↦ (n + 2 : ℝ) * f s ^ (n + 1) * deriv f s) := by
    filter_upwards [hf.eventually (by norm_num)] with s hs
    simpa only [Nat.cast_add, Nat.cast_ofNat, show n + 2 - 1 = n + 1 by omega] using
      ((hs.differentiableAt (by norm_num)).hasDerivAt.fun_pow (n + 2)).deriv
  rw [he.deriv_eq]
  have hd := (hf.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have h := (((hd.fun_pow (n + 1)).const_mul (n + 2 : ℝ)).mul hdd).deriv
  exact h.trans (by simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]; ring)

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
