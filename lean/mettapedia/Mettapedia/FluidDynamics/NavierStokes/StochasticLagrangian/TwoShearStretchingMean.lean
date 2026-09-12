import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearStretchingJet
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicMean
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Positive mean stretching production from zero initial stretching

For the NS-compatible initial jet of `TwoShearStretchingJet`, the actual
normalized three-dimensional spatial mean of the eighth-moment stretching
density is zero initially and has initial derivative `125 / 128 > 0`.

The means are Lebesgue integrals over `[0, 2π]³`. Differentiation of the
mean is proved using the explicit factor `t` and continuity of the remaining
mean, rather than an unproved interchange of differentiation and integration.
As in the jet construction, this is an initial-time obstruction to a
multiplicative sign law, not a positive-time NS solution or a blowup result.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearStretchingMean

open Real Filter PancakePeriodicMean TwoShearStretchingJet
open scoped Topology

def point (x y z : ℝ) : NSSpace :=
  EuclideanSpace.single 0 x + EuclideanSpace.single 1 y + EuclideanSpace.single 2 z

/-- Normalized Lebesgue mean on the full periodic cube, including the third coordinate. -/
def meanStretching (ν t : ℝ) : ℝ :=
  spatialMean (fun x y => circleMean (fun z => eighthStretchingDensity ν t (point x y z)))

private def densityFactor (ν t x y : ℝ) : ℝ :=
  vorticityNormSq ν t (point x y 0) ^ 3 * (1 - ν * t) * cos y ^ 2 * cos x *
    ((1 - ν * t) * cos x + t * sin y * sin x)

private theorem density_eq_factor (ν t x y z : ℝ) :
    eighthStretchingDensity ν t (point x y z) = t * densityFactor ν t x y := by
  simp [eighthStretchingDensity_eq, densityFactor, vorticityNormSq, point]

private theorem meanStretching_eq (ν t : ℝ) :
    meanStretching ν t = t * spatialMean (densityFactor ν t) := by
  unfold meanStretching
  simp_rw [density_eq_factor, circleMean_const]
  exact spatialMean_const_mul t (densityFactor ν t)

@[simp] theorem meanStretching_zero (ν : ℝ) : meanStretching ν 0 = 0 := by
  simp [meanStretching_eq]

private theorem continuous_factor_mean (ν : ℝ) :
    Continuous (fun t => spatialMean (densityFactor ν t)) := by
  apply continuous_spatialMean
  simp [densityFactor, vorticityNormSq, point]
  fun_prop

private theorem factor_mean_zero (ν : ℝ) :
    spatialMean (densityFactor ν 0) = 125 / 128 := by
  have heq : ∀ x y, densityFactor ν 0 x y =
      cos x ^ 8 * cos y ^ 2 + 3 * (cos x ^ 6 * cos y ^ 4) +
        3 * (cos x ^ 4 * cos y ^ 6) + cos x ^ 2 * cos y ^ 8 := by
    intro x y
    simp [densityFactor, vorticityNormSq, point]
    ring
  rw [spatialMean_congr _ _ heq]
  repeat' rw [spatialMean_add _ _ (by fun_prop) (by fun_prop)]
  simp only [spatialMean_const_mul, spatialMean_product, circleMean_cos_sq,
    circleMean_cos_pow_four, circleMean_cos_pow_six, circleMean_cos_pow_eight]
  norm_num

/-- Multiplication by the vanishing time factor only requires continuity
of the other factor to compute the derivative at zero. -/
private theorem hasDerivAt_mul_identity_zero (g : ℝ → ℝ) (hg : ContinuousAt g 0) :
    HasDerivAt (fun t => t * g t) (g 0) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (hg.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  simp [slope, ht0, smul_eq_mul]

/-- Exact derivative of the spatial mean, not merely a mean of pointwise rates. -/
theorem hasDerivAt_meanStretching_zero (ν : ℝ) :
    HasDerivAt (meanStretching ν) (125 / 128) 0 := by
  have h := hasDerivAt_mul_identity_zero (fun t => spatialMean (densityFactor ν t))
    (continuous_factor_mean ν).continuousAt
  rw [factor_mean_zero] at h
  have heq : (fun t => t * spatialMean (densityFactor ν t)) = meanStretching ν := by
    funext t
    exact (meanStretching_eq ν t).symm
  rwa [heq] at h

theorem initial_mean_rate (ν : ℝ) : deriv (meanStretching ν) 0 = 125 / 128 :=
  (hasDerivAt_meanStretching_zero ν).deriv

theorem initial_mean_rate_pos (ν : ℝ) : 0 < deriv (meanStretching ν) 0 := by
  rw [initial_mean_rate]
  norm_num

/-- Spatial averaging does not restore a multiplicative zero-source damping law. -/
theorem not_initial_mean_multiplicative_damping (ν b : ℝ) :
    ¬ deriv (meanStretching ν) 0 ≤ b * meanStretching ν 0 := by
  rw [initial_mean_rate, meanStretching_zero]
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.TwoShearStretchingMean
