import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Local linearity of second derivatives; only local `C²` regularity is used. -/

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

end Mettapedia.Analysis
