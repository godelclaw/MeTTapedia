import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SquaredGapTiltWeight

/-!
# A fourth-power gap gate for two-input weight factorization

An additional squared gate regularizes the square root used on each
vorticity input. Its cost is retained in the transition/collision term.
The new weight agrees with the old weight where the gap ramp is one.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.QuarticGapTiltWeight

open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open SpectralGapTiltWeight SpectralDiffusionWeightLimit SpectralTiltFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def weight (gamma : ℝ) (S : SymmetricStrain) (w : R3) : ℝ :=
  gapCutoff gamma (topGap S) ^ 2 * SquaredGapTiltWeight.weight gamma S w

def collisionCost (gamma : ℝ) (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  (1 - gapCutoff gamma (topGap S) ^ 4) * (2 * ‖R‖ * ‖w‖ ^ 2)

theorem weight_nonneg (gamma : ℝ) (S : SymmetricStrain) (w : R3) : 0 ≤ weight gamma S w :=
  mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem weight_le_squaredGapWeight (gamma : ℝ) (S : SymmetricStrain) (w : R3) :
    weight gamma S w ≤ SquaredGapTiltWeight.weight gamma S w := by
  have h0 := gapCutoff_nonneg gamma (topGap S)
  have h1 := gapCutoff_le_one gamma (topGap S)
  exact (mul_le_mul_of_nonneg_right (by nlinarith : gapCutoff gamma (topGap S) ^ 2 ≤ 1)
    (sq_nonneg (SquaredGapTiltWeight.amplitude gamma S w))).trans_eq (one_mul _)

theorem collisionCost_eq_squared_add (gamma : ℝ) (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) :
    collisionCost gamma S R w = SquaredGapTiltWeight.collisionCost gamma S R w +
      gapCutoff gamma (topGap S) ^ 2 * (1 - gapCutoff gamma (topGap S) ^ 2) *
        (2 * ‖R‖ * ‖w‖ ^ 2) := by
  unfold collisionCost SquaredGapTiltWeight.collisionCost
  ring

theorem weight_eq_of_gate_one (gamma : ℝ) (S : SymmetricStrain) (w : R3)
    (h : gapCutoff gamma (topGap S) = 1) : weight gamma S w = SquaredGapTiltWeight.weight gamma S w := by
  simp [weight, h]

theorem excess_le_weighted_tilt_add_collision (gamma : ℝ) (hg : 0 < gamma)
    (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    SpectralTiltExcess.excess S R w ≤
      gapCutoff gamma (topGap S) ^ 4 *
        (max (2 * ‖R‖ - topGap S ^ 2 / 8) 0 * limitingWeight S w) +
      8 * weight gamma S w * SpectralTiltExcess.tiltNorm S R ^ 2 + collisionCost gamma S R w := by
  have h0 := gapCutoff_nonneg gamma (topGap S)
  have h1 := gapCutoff_le_one gamma (topGap S)
  have hgate : 0 ≤ 1 - gapCutoff gamma (topGap S) ^ 2 := by nlinarith
  have hs := mul_le_mul_of_nonneg_left
    (SquaredGapTiltWeight.excess_le_weighted_tilt_add_collision gamma hg S R w)
    (sq_nonneg (gapCutoff gamma (topGap S)))
  have hc := mul_le_mul_of_nonneg_left (SpectralTiltExcess.excess_le_coarse S R w) hgate
  unfold SquaredGapTiltWeight.collisionCost at hs
  unfold weight collisionCost
  nlinarith only [hs, hc]

end Mettapedia.FluidDynamics.NavierStokes.QuarticGapTiltWeight
