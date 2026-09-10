import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralCommutatorLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralDiffusionExcess

/-!
# Source absorption by spectral residual dissipation

A quarter of the squared spectral residual pays the quadratic source below
a squared-gap threshold and a Young inequality for the source commutator.
The remaining cost is capped by the original anisotropy envelope. This cap
preserves integrability near spectral collisions and vanishing at alignment.
No global bound on the excess, or positive lower bound on the gap, is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess

open scoped RealInnerProductSpace
open MeasureTheory
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralDefectEvolution PancakeSpectralFiniteDifference
open SpectralSourceCommutator SpectralCommutatorLimit SpectralDiffusionWeightLimit
open SpectralDiffusionExcess StrainEigenvalueContinuity

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The uncapped simple-gap cost after spending a quarter of the residual. -/
def refinedCost (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  max (2 * ‖R‖ - topGap S ^ 2 / 8) 0 * limitingWeight S w +
    8 * (‖commutator S R‖ / topGap S ^ 2) ^ 2 * ‖w‖ ^ 2

/-- The collision-safe source cost that remains after absorption. -/
def excess (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  if 0 < topGap S then min (limitingEnvelope S R w) (refinedCost S R w)
  else limitingEnvelope S R w

theorem refinedCost_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    0 ≤ refinedCost S R w := by
  have hw := limitingWeight_nonneg S w
  unfold refinedCost
  positivity

theorem excess_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    0 ≤ excess S R w := by
  unfold excess
  split
  · exact le_min (limitingEnvelope_nonneg S R w) (refinedCost_nonneg S R w)
  · exact limitingEnvelope_nonneg S R w

theorem excess_le_envelope (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    excess S R w ≤ limitingEnvelope S R w := by
  unfold excess
  split
  · exact min_le_left _ _
  · exact le_rfl

theorem excess_le_coarse (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    excess S R w ≤ 2 * ‖R‖ * ‖w‖ ^ 2 :=
  (excess_le_envelope S R w).trans (limitingEnvelope_le_coarse S R w)

theorem tilt_le_eighth_residual_add_commutator_cost (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (hg : 0 < topGap S) :
    2 * (‖commutator S R‖ / topGap S) * ‖w‖ * Real.sqrt (limitingWeight S w) ≤
      ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 / 8 +
        8 * (‖commutator S R‖ / topGap S ^ 2) ^ 2 * ‖w‖ ^ 2 := by
  have hs := Real.sq_sqrt (limitingWeight_nonneg S w)
  have hq := topGap_sq_mul_limitingWeight_le_residual S w
  have hid :
      (topGap S * Real.sqrt (limitingWeight S w)) *
        (‖commutator S R‖ / topGap S ^ 2 * ‖w‖) =
      (‖commutator S R‖ / topGap S) * ‖w‖ * Real.sqrt (limitingWeight S w) := by
    field_simp
  have hsq := sq_nonneg (topGap S * Real.sqrt (limitingWeight S w) -
    8 * (‖commutator S R‖ / topGap S ^ 2 * ‖w‖))
  have hq' : (topGap S * Real.sqrt (limitingWeight S w)) ^ 2 ≤
      ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 := by
    rw [mul_pow, hs]
    exact hq
  nlinarith only [hsq, hq', hid]

theorem envelope_le_quarter_residual_add_refinedCost (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (hg : 0 < topGap S) :
    limitingEnvelope S R w ≤ ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 / 4 +
      refinedCost S R w := by
  have hE := limitingEnvelope_le_refined S R w hg
  have hT := tilt_le_eighth_residual_add_commutator_cost S R w hg
  have hQ := topGap_sq_mul_limitingWeight_le_residual S w
  have hM := mul_le_mul_of_nonneg_right (le_max_left (2 * ‖R‖ - topGap S ^ 2 / 8) 0)
    (limitingWeight_nonneg S w)
  unfold refinedCost
  linarith only [hE, hT, hQ, hM]

theorem envelope_le_quarter_residual_add_excess (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) :
    limitingEnvelope S R w ≤ ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 / 4 +
      excess S R w := by
  have hQ : 0 ≤ ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 / 4 := by positivity
  unfold excess
  split_ifs with hg
  · rw [add_min]
    exact le_min (by linarith) (envelope_le_quarter_residual_add_refinedCost S R w hg)
  · linarith

theorem excess_eq_coarse_of_topGap_zero (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (w : R3) (hg : topGap S = 0) : excess S R w = 2 * ‖R‖ * ‖w‖ ^ 2 := by
  simp only [excess, hg, lt_self_iff_false, if_false,
    limitingEnvelope_eq_coarse_of_topGap_zero S R w hg]

theorem excess_aligned (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (c : ℝ)
    (hg : 0 < topGap S) : excess S R (c • topVector S) = 0 :=
  le_antisymm (by simpa only [limitingEnvelope_aligned S R c hg] using
    excess_le_envelope S R (c • topVector S)) (excess_nonneg _ _ _)

theorem excess_le_commutator_cost_of_le (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (w : R3) (hg : 0 < topGap S) (hR : 16 * ‖R‖ ≤ topGap S ^ 2) :
    excess S R w ≤ 8 * (‖commutator S R‖ / topGap S ^ 2) ^ 2 * ‖w‖ ^ 2 := by
  have hm : 2 * ‖R‖ - topGap S ^ 2 / 8 ≤ 0 := by linarith
  rw [excess, if_pos hg, refinedCost, max_eq_right hm, zero_mul, zero_add]
  exact min_le_right _ _

/-- A commuting source below the explicit threshold is paid in full. -/
theorem excess_eq_zero_of_commutator_eq_zero (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (hg : 0 < topGap S)
    (hc : commutator S R = 0) (hR : 16 * ‖R‖ ≤ topGap S ^ 2) :
    excess S R w = 0 := by
  have hm : 2 * ‖R‖ - topGap S ^ 2 / 8 ≤ 0 := by linarith
  simp only [excess, if_pos hg, refinedCost, max_eq_right hm, zero_mul, hc,
    norm_zero, zero_div, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    min_eq_right (limitingEnvelope_nonneg S R w)]

theorem measurable_excess {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X → SymmetricStrain) (R : X → R3 →L[ℝ] R3) (w : X → R3)
    (hS : Continuous S) (hR : Continuous R) (hw : Continuous w) :
    Measurable (fun x ↦ excess (S x) (R x) (w x)) := by
  have hgap := (continuous_topGap.comp hS).measurable
  have hE := measurable_limitingEnvelope S R w hS hR hw
  have hW := measurable_limitingWeight S w hS hw
  have hJ := (continuous_commutator S R hS hR).norm.measurable
  have hF : Measurable (fun x ↦ refinedCost (S x) (R x) (w x)) :=
    ((((measurable_const.mul hR.norm.measurable).sub ((hgap.pow_const 2).div_const 8)).max
      measurable_const).mul hW).add
      ((measurable_const.mul ((hJ.div (hgap.pow_const 2)).pow_const 2)).mul (hw.norm.pow 2).measurable)
  exact Measurable.ite (measurableSet_lt measurable_const hgap) (hE.min hF) hE

end Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess
