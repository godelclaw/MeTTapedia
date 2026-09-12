import Mettapedia.Analysis.WeightedCrossProductEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TraceFreeStrainAngle

/-!
# Spectral gap and amplitude growth in the weighted angular rate

The same bottom-eigenvalue bound that damps the normalized angle leaves
amplitude growth in the weighted cost. Weighted top spectral defects are
retained with their favorable sign. No inverse gap or nonzero-vorticity
hypothesis is needed. The common-strain coefficient is a growth bound,
not a claimed lower bound for the actual rate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TraceFreeWeightedAngularRate

open Mettapedia.Analysis WeightedCrossProduct EuclideanCrossProduct
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralDefectEvolution StrainEigenvalueContinuity PancakeStrainSpectralFrame
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def weightedTopDefect (n : ℕ) (S T : SymmetricStrain) (a b : R3) : ℝ :=
  ‖a‖ ^ (2 * n) * topSpectralDefect S a + ‖b‖ ^ (2 * n) * topSpectralDefect T b

def growthWeight (n : ℕ) (S T : SymmetricStrain) (a b : R3) : ℝ :=
  (2 * (n + 1) : ℝ) * (topEigenvalue S * ‖a‖ ^ (2 * (n + 1)) +
    topEigenvalue T * ‖b‖ ^ (2 * (n + 1))) +
      (2 * (topEigenvalue S + topEigenvalue T) - (topGap S + topGap T)) * amplitudeWeight n a b

theorem weightedTopDefect_nonneg (n : ℕ) (S T : SymmetricStrain) (a b : R3) :
    0 ≤ weightedTopDefect n S T a b := by
  unfold weightedTopDefect
  positivity [topSpectralDefect_nonneg S a, topSpectralDefect_nonneg T b]

theorem amplitudeRate_eq_growth_sub_defect (n : ℕ) (S T : SymmetricStrain) (a b : R3) :
    amplitudeRate n a b (S.1 a) (T.1 b) = (2 * (n + 1) : ℝ) *
      (topEigenvalue S * ‖a‖ ^ (2 * (n + 1)) + topEigenvalue T * ‖b‖ ^ (2 * (n + 1)) -
        weightedTopDefect n S T a b) := by
  simp only [amplitudeRate, weightedTopDefect, topSpectralDefect, spectralDefect,
    show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  ring

theorem strainRate_add_defect_le_growth (n : ℕ) (S T : SymmetricStrain)
    (hS : LinearMap.trace ℝ R3 S.1.toLinearMap = 0)
    (hT : LinearMap.trace ℝ R3 T.1.toLinearMap = 0) (a b : R3) :
    strainRate n S.1 T.1 a b +
      (2 * (n + 1) : ℝ) * weightedTopDefect n S T a b * ‖cross a b‖ ^ 2 ≤
        growthWeight n S T a b * ‖cross a b‖ ^ 2 := by
  have hs := TraceFreeStrainAngle.topGap_sub_two_topEigenvalue_le_rayleigh S hS (cross a b)
  have ht := TraceFreeStrainAngle.topGap_sub_two_topEigenvalue_le_rayleigh T hT (cross a b)
  have hm := mul_le_mul_of_nonneg_left (add_le_add hs ht) (amplitudeWeight_nonneg n a b)
  unfold strainRate
  rw [amplitudeRate_eq_growth_sub_defect]
  unfold growthWeight
  nlinarith only [hm]

def commonGrowthCoefficient (n : ℕ) (S : SymmetricStrain) : ℝ :=
  ((2 * (n + 1) : ℝ) + 4) * topEigenvalue S - 2 * topGap S

theorem growthWeight_common (n : ℕ) (S : SymmetricStrain) (a b : R3) :
    growthWeight n S S a b = commonGrowthCoefficient n S * amplitudeWeight n a b := by
  unfold growthWeight commonGrowthCoefficient amplitudeWeight
  ring

/-- The upper-bound coefficient is not a damping coefficient. This does
not assert that every vector pair has positive weighted energy rate. -/
theorem commonGrowthCoefficient_lower_bound (n : ℕ) (S : SymmetricStrain)
    (hS : LinearMap.trace ℝ R3 S.1.toLinearMap = 0) :
    ((2 * (n + 1) : ℝ) + 1) * topEigenvalue S ≤ commonGrowthCoefficient n S := by
  rw [trace_eq_sum_orderedEigenvalues] at hS
  have h12 : thirdEigenvalue S ≤ secondEigenvalue S :=
    (orderedEigenframe S.1 S.2).antitone_eigenvalue (by decide)
  unfold commonGrowthCoefficient topGap
  nlinarith only [h12, hS]

theorem commonGrowthCoefficient_eighth (S : SymmetricStrain) :
    commonGrowthCoefficient 2 S = 10 * topEigenvalue S - 2 * topGap S := by
  unfold commonGrowthCoefficient
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.TraceFreeWeightedAngularRate
