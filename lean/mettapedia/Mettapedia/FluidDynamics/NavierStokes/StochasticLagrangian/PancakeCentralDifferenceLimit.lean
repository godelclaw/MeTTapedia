import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Central spatial differences of a twice continuously differentiable curve

Taylor's theorem identifies the central quotient with the actual second
derivative. This lemma concerns the smooth strain and vorticity curves,
not the generally nonsmooth largest eigenvalue.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCentralDifferenceLimit

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def centralDifference (f : ℝ → E) (h : ℝ) : E :=
  (h ^ 2)⁻¹ • (f h + f (-h) - (2 : ℝ) • f 0)

theorem taylor_two_at_zero (f : ℝ → E) (h : ℝ) :
    taylorWithinEval f 2 univ 0 h =
      f 0 + h • deriv f 0 + ((1 / 2 : ℝ) * h ^ 2) • deriv (deriv f) 0 := by
  simp [show 2 = 1 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval,
    iteratedDerivWithin_univ, iteratedDeriv_succ]
  norm_num

theorem centralDifference_tendsto (f : ℝ → E) (hf : ContDiff ℝ 2 f) :
    Tendsto (centralDifference f) (𝓝[≠] (0 : ℝ)) (𝓝 (deriv (deriv f) 0)) := by
  let R : ℝ → E := fun h ↦ (h ^ 2)⁻¹ • (f h - taylorWithinEval f 2 univ 0 h)
  have hr : Tendsto R (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [R, sub_zero, nhdsWithin_univ] using
      (taylor_tendsto (f := f) (n := 2) convex_univ (mem_univ (0 : ℝ)) hf.contDiffOn)
  have hm : Tendsto (fun h ↦ R (-h)) (𝓝 (0 : ℝ)) (𝓝 0) :=
    hr.comp (by simpa using (tendsto_id.neg : Tendsto (fun h : ℝ ↦ -h) (𝓝 0) (𝓝 (-0))))
  have hall : Tendsto (fun h ↦ R h + R (-h) + deriv (deriv f) 0)
      (𝓝 (0 : ℝ)) (𝓝 (deriv (deriv f) 0)) := by
    simpa only [zero_add] using (hr.add hm).add_const (deriv (deriv f) 0)
  apply (hall.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := hh
  have hsq : (h ^ 2)⁻¹ * h ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hh0)
  dsimp only [R, centralDifference]
  rw [taylor_two_at_zero, taylor_two_at_zero]
  simp only [neg_sq, neg_smul, smul_add, smul_sub, smul_smul]
  have hhf : (h ^ 2)⁻¹ * ((1 / 2 : ℝ) * h ^ 2) = 1 / 2 := by field_simp
  rw [hhf]
  module

end Mettapedia.FluidDynamics.NavierStokes.PancakeCentralDifferenceLimit
