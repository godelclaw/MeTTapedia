import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MonochromaticShearProjection
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionMean

/-!
# The exact coercivity threshold on an unforced monochromatic shear

The weighted projection energy is exactly `eigenvalue * E8 / 7`, for
every regularization parameter. The identity follows from the actual
spatial energy balance, not numerical quadrature. Matching the correction
normalization to the Laplacian eigenvalue therefore gives negative energy.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MonochromaticShearProjection

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget LocalAlignmentForcing
open LocalVorticityEighthMoment LocalWeightedProjectionEvolution LocalHelicityProjectionEvolution
open LocalHelicityProjectionDiffusion
open GaussianRootWeightedIncrement FilteredProjectionMean FourierFiniteSupport

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_vorticity_sq (A : ℝ) (x : T3) :
    ‖fullVorticity (velocity A) x‖ ^ 2 = ((2 * Real.pi) * A * cosine x) ^ 2 := by
  rw [vorticity_eq, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three, Matrix.cons_val_two]

theorem radialDensity_eq_weightedPalinstrophyDensity (A : ℝ) (x : T3) :
    radialGradientDensity (velocity A) x = weightedPalinstrophyDensity (velocity A) x := by
  simp only [radialGradientDensity, weightedPalinstrophyDensity,
    show ∀ r : ℝ, r ^ 6 = (r ^ 2) ^ 3 from by intro r; ring,
    show ∀ r : ℝ, r ^ 4 = (r ^ 2) ^ 2 from by intro r; ring,
    vorticity_eq, vorticityGradient_eq]
  simp +decide [EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

theorem projectionDensity_eq_weightedPalinstrophyDensity (δ A : ℝ) (x : T3) :
    weightedProjectionDensity δ (velocity A) x = weightedPalinstrophyDensity (velocity A) x := by
  have hi : ⟪fullVorticity (velocity A) x, fullVorticity (fourierCurl (velocity A)) x⟫ = 0 := by
    rw [vorticity_eq, doubleCurl_eq]
    simp [PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  simp only [weightedProjectionDensity, projectionEnergy, RegularizedProjection.energy,
    RegularizedProjection.residual, RegularizedProjection.coefficient, hi,
    zero_div, zero_smul, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  unfold weightedPalinstrophyDensity
  congr 1
  rw [doubleCurl_eq]
  simp +decide [vorticityGradient_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Matrix.cons_val_two]

theorem radialDissipation_eq_weightedPalinstrophy (A : ℝ) :
    radialDissipation (velocity A) = weightedPalinstrophy (velocity A) := by
  simp only [radialDissipation, weightedPalinstrophy, radialDensity_eq_weightedPalinstrophyDensity]

theorem projectionEnergy_eq_weightedPalinstrophy (δ A : ℝ) :
    weightedProjectionEnergy δ (velocity A) = weightedPalinstrophy (velocity A) := by
  simp only [weightedProjectionEnergy, weightedPalinstrophy, projectionDensity_eq_weightedPalinstrophyDensity]

theorem materialRate_eq (A : ℝ) (x : T3) :
    materialRate (velocity A) 1 x = (-8 * eigenvalue) * LocalVorticityEighthMoment.energy (velocity A) x := by
  have hs := ParallelHeatFlow.fullStrain_apply_vorticity_eq_zero (scalarData A) (horizontal A) x
  change fullStrainOperator (velocity A) x (fullVorticity (velocity A) x) = 0 at hs
  simp only [LocalVorticityEighthMoment.materialRate, hs, vorticityLaplacian_eq, one_smul, zero_add,
    real_inner_smul_right, real_inner_self_eq_norm_sq, energy_eq_norm_pow]
  ring

/-- The factor seven is the sum of the tangential coefficient one and
the radial coefficient six in the octic dissipation identity. -/
theorem seven_mul_weightedPalinstrophy (A : ℝ) :
    7 * weightedPalinstrophy (velocity A) = eigenvalue * meanEnergy (velocity A) := by
  have h := integral_materialRate_add_dissipation_eq (velocity A) 1
    (summable_fourierMoment modes _ (supported A) 3)
  simp only [materialRate_eq, integral_const_mul, one_mul, mul_one] at h
  change (-8 * eigenvalue) * meanEnergy (velocity A) / 8 + weightedPalinstrophy (velocity A) +
    6 * radialDissipation (velocity A) = stretching (velocity A) at h
  rw [radialDissipation_eq_weightedPalinstrophy,
    show stretching (velocity A) = 0 from ParallelHeatFlow.stretching_eq_zero (scalarData A) (horizontal A)] at h
  linarith only [h]

theorem correctedMean_eq (δ κ A : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    meanCorrectedEnergy δ κ (velocity A) =
      ((7 * κ - 24 * eigenvalue) / (56 * κ)) * meanEnergy (velocity A) := by
  rw [FilteredProjectionMean.meanCorrectedEnergy_eq δ hδ κ modes _ (supported A),
    projectionEnergy_eq_weightedPalinstrophy]
  have h := seven_mul_weightedPalinstrophy A
  field_simp [ne_of_gt hκ]
  nlinarith only [h]

theorem matched_correctedMean_eq (δ A : ℝ) (hδ : 0 < δ) :
    meanCorrectedEnergy δ eigenvalue (velocity A) = -17 / 56 * meanEnergy (velocity A) := by
  rw [correctedMean_eq δ eigenvalue A hδ eigenvalue_pos]
  congr 1
  field_simp [ne_of_gt eigenvalue_pos]
  ring

end Mettapedia.FluidDynamics.NavierStokes.MonochromaticShearProjection
