import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialSpatialEstimate
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Differentiating a compact spatial mean

Joint continuity makes the actual parameter derivative measurable. A
spatially uniform local Lipschitz bound permits differentiation under the
integral at parameters with almost-everywhere spatial differentiability.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCompactMeanDerivative

open scoped Topology NNReal
open MeasureTheory Filter

variable {P : Type*} [TopologicalSpace P] [CompactSpace P]
  [MeasureSpace P] [BorelSpace P] [IsProbabilityMeasure (volume : Measure P)]

def parameterRate (f : ℝ → P → ℝ) (t : ℝ) (x : P) : ℝ := deriv (fun h ↦ f h x) t

omit [CompactSpace P] [IsProbabilityMeasure (volume : Measure P)] in
theorem measurable_parameterRate (f : ℝ → P → ℝ)
    (hf : Continuous f.uncurry) (t : ℝ) : Measurable (parameterRate f t) := by
  have hm : Measurable (fun z : P × ℝ ↦ deriv (fun h ↦ f h z.1) z.2) :=
    measurable_deriv_with_param (f := fun x : P ↦ fun h : ℝ ↦ f h x) (hf.comp continuous_swap)
  exact hm.comp (show Measurable (fun x : P ↦ (x, t)) from measurable_id.prodMk measurable_const)

theorem integrable_slice (f : ℝ → P → ℝ) (hf : Continuous f.uncurry) (t : ℝ) :
    Integrable (f t) :=
  (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem hasDerivAt_mean_of_uniform_lipschitz
    (f : ℝ → P → ℝ) (hf : Continuous f.uncurry) (t : ℝ)
    (s : Set ℝ) (hs : s ∈ 𝓝 t) (C : ℝ≥0)
    (hlip : ∀ x, LipschitzOnWith C (fun h ↦ f h x) s)
    (hd : ∀ᵐ x : P, DifferentiableAt ℝ (fun h ↦ f h x) t) :
    Integrable (parameterRate f t) ∧
      HasDerivAt (fun h ↦ ∫ x : P, f h x) (∫ x : P, parameterRate f t x) t := by
  apply hasDerivAt_integral_of_dominated_loc_of_lip (bound := fun _ : P ↦ (C : ℝ)) hs
  · exact Filter.Eventually.of_forall (fun h ↦ (integrable_slice f hf h).aestronglyMeasurable)
  · exact integrable_slice f hf t
  · exact (measurable_parameterRate f hf t).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x ↦ by simpa only [Real.nnabs_coe] using hlip x)
  · exact integrable_const _
  · exact hd.mono (fun _ hx ↦ hx.hasDerivAt)

theorem lipschitzOnWith_mean (f : ℝ → P → ℝ) (hf : Continuous f.uncurry)
    (s : Set ℝ) (C : ℝ≥0) (hlip : ∀ x, LipschitzOnWith C (fun h ↦ f h x) s) :
    LipschitzOnWith C (fun h ↦ ∫ x : P, f h x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  rw [dist_eq_norm, ← integral_sub (integrable_slice f hf a) (integrable_slice f hf b)]
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure P))
    (Filter.Eventually.of_forall (fun x : P ↦ (hlip x).norm_sub_le ha hb))
  simpa only [probReal_univ, mul_one, dist_eq_norm] using h

end Mettapedia.FluidDynamics.NavierStokes.PancakeCompactMeanDerivative
