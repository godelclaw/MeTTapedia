import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MonochromaticShearEvolution

/-! Exact regression tests for the normalization threshold and angular separation. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MonochromaticShearTests

open MonochromaticShearProjection FilteredProjectionMean LocalWeightedProjectionEvolution
open LocalVorticityEighthMoment

theorem threshold_has_zero_correctedMean (δ A : ℝ) (hδ : 0 < δ) :
    meanCorrectedEnergy δ (24 / 7 * eigenvalue) (velocity A) = 0 := by
  rw [correctedMean_eq δ _ A hδ (mul_pos (by norm_num : (0 : ℝ) < 24 / 7) eigenvalue_pos)]
  have he : 7 * (24 / 7 * eigenvalue) - 24 * eigenvalue = 0 := by ring
  rw [he, zero_div, zero_mul]

theorem doubled_threshold_has_half_margin (δ A : ℝ) (hδ : 0 < δ) :
    meanCorrectedEnergy δ (48 / 7 * eigenvalue) (velocity A) = meanEnergy (velocity A) / 16 := by
  rw [correctedMean_eq δ _ A hδ (mul_pos (by norm_num : (0 : ℝ) < 48 / 7) eigenvalue_pos)]
  field_simp [ne_of_gt eigenvalue_pos]
  ring

theorem positive_viscosity_matched_negative :
    meanCorrectedEnergy 1 eigenvalue ((heatSolution (ν := 1) (by norm_num) 1 1).coefficients (1 / 2)) < 0 :=
  heatSolution_matched_correctedMean_neg (by norm_num) 1 1 1 (1 / 2) (by norm_num) (by norm_num)

theorem positive_viscosity_angular_separation :
    LocalAngularCurlBudget.angularCurlEnergy
        ((heatSolution (ν := 1) (by norm_num) 1 1).coefficients (1 / 2)) = 0 ∧
      0 < weightedProjectionEnergy 1 ((heatSolution (ν := 1) (by norm_num) 1 1).coefficients (1 / 2)) :=
  heatSolution_angular_projection_separation (by norm_num) 1 1 1 (1 / 2) (by norm_num)

theorem no_uniform_angular_payment (C : ℝ) :
    ¬ weightedProjectionEnergy 1 (velocity 1) ≤
      C * (weightedPalinstrophy (velocity 1) - radialDissipation (velocity 1)) :=
  not_projectionEnergy_le_angularDissipation 1 1 C (by norm_num)

end Mettapedia.FluidDynamics.NavierStokes.MonochromaticShearTests
