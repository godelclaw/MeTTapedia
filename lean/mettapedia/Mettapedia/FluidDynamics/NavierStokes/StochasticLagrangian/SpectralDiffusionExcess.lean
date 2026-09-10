import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralDiffusionWeightLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralResidualDepletion

/-!
# The excess diffusion cost after coherent spectral damping

The capped limiting weight obeys the same squared-gap coercivity as the
transverse square. This permits a pointwise good/bad split without any
global positive-gap assumption. At collisions the full diffusion cost
remains in the excess.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralDiffusionExcess

open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralDefectEvolution PancakeSpectralResidualDepletion SpectralDiffusionWeightLimit
open StrainEigenvalueContinuity

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem topGap_sq_mul_limitingWeight_le_residual (S : SymmetricStrain) (w : R3) :
    topGap S ^ 2 * limitingWeight S w ≤ ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 := by
  apply le_trans ?_ (topGap_mul_defect_le_norm_topSpectralResidual_sq S w)
  by_cases hg : 0 < topGap S
  · have hw : limitingWeight S w ≤ topSpectralDefect S w / topGap S := by
      simp only [limitingWeight, if_pos hg]
      exact min_le_right _ _
    have h := mul_le_mul_of_nonneg_left ((le_div_iff₀ hg).mp hw) hg.le
    nlinarith only [h]
  · have hz : topGap S = 0 := le_antisymm (le_of_not_gt hg) (topGap_nonneg S)
    simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl]

def excess (S : SymmetricStrain) (w : R3) (a : ℝ) : ℝ :=
  max (a - topGap S ^ 2 / 2) 0 * limitingWeight S w

theorem excess_nonneg (S : SymmetricStrain) (w : R3) (a : ℝ) : 0 ≤ excess S w a :=
  mul_nonneg (le_max_right _ _) (limitingWeight_nonneg S w)

theorem excess_le_cost (S : SymmetricStrain) (w : R3) (a : ℝ) (ha : 0 ≤ a) :
    excess S w a ≤ a * limitingWeight S w := by
  apply mul_le_mul_of_nonneg_right (max_le ?_ ha) (limitingWeight_nonneg S w)
  linarith [sq_nonneg (topGap S)]

theorem cost_le_half_residual_add_excess (S : SymmetricStrain) (w : R3) (a : ℝ) :
    a * limitingWeight S w ≤ ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 / 2 + excess S w a := by
  have h := mul_le_mul_of_nonneg_right (le_max_left (a - topGap S ^ 2 / 2) 0)
    (limitingWeight_nonneg S w)
  have hz := topGap_sq_mul_limitingWeight_le_residual S w
  unfold excess
  nlinarith only [h, hz]

theorem excess_eq_zero_of_le (S : SymmetricStrain) (w : R3) (a : ℝ)
    (ha : 2 * a ≤ topGap S ^ 2) : excess S w a = 0 := by
  rw [excess, max_eq_right (by linarith), zero_mul]

theorem excess_eq_cost_of_topGap_zero (S : SymmetricStrain) (w : R3) (a : ℝ)
    (ha : 0 ≤ a) (hg : topGap S = 0) : excess S w a = a * ‖w‖ ^ 2 := by
  simp only [excess, hg, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, max_eq_left ha,
    limitingWeight_eq_norm_sq_of_topGap_zero S w hg]

theorem measurable_excess {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X → SymmetricStrain) (w : X → R3) (a : X → ℝ)
    (hS : Continuous S) (hw : Continuous w) (ha : Continuous a) :
    Measurable (fun x ↦ excess (S x) (w x) (a x)) :=
  ((ha.sub (((continuous_topGap.comp hS).pow 2).div_const 2)).max continuous_const).measurable.mul
    (measurable_limitingWeight S w hS hw)

end Mettapedia.FluidDynamics.NavierStokes.SpectralDiffusionExcess
