import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MonochromaticShearCoercivity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAngularCurlBudget

/-!
# Coercivity and angular variation along an exact unforced shear

The shear solves the full infinite Fourier Navier–Stokes equation on every
finite forward interval. Its octic moment is positive at every finite time
for positive initial amplitude. Spectrally matched projection correction
is therefore negative along an actual solution, despite zero stretching
and zero angular dissipation. This excludes that correction as a positive
energy at the matched normalization, not the regularity of the solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MonochromaticShearProjection

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeLocalInfiniteVelocity
open LocalLowDiffusionBudget LocalVorticityEighthMoment LocalWeightedProjectionEvolution
open LocalHelicityProjectionEvolution FourierFiniteSupport FilteredProjectionMean

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem cosine_zero : cosine 0 = 1 := by simp [cosine, UnitAddTorus.mFourier]

theorem meanEnergy_pos (A : ℝ) (hA : 0 < A) : 0 < meanEnergy (velocity A) := by
  have hc : Continuous (LocalVorticityEighthMoment.energy (velocity A)) :=
    ((continuous_fullVorticity _ (summable_fourierMoment modes _ (supported A) 1)).norm.pow 2).pow 4
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun x ↦ by unfold energy; positivity)
  show LocalVorticityEighthMoment.energy (velocity A) 0 ≠ 0
  simp only [LocalVorticityEighthMoment.energy, norm_vorticity_sq, cosine_zero, mul_one]
  positivity

theorem matched_correctedMean_neg (δ A : ℝ) (hδ : 0 < δ) (hA : 0 < A) :
    meanCorrectedEnergy δ eigenvalue (velocity A) < 0 := by
  rw [matched_correctedMean_eq δ A hδ]
  exact mul_neg_of_neg_of_pos (by norm_num) (meanEnergy_pos A hA)

/-- Exact threshold, stronger than a failure at one parameter value. -/
theorem correctedMean_nonneg_iff (δ κ A : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) (hA : 0 < A) :
    0 ≤ meanCorrectedEnergy δ κ (velocity A) ↔ 24 * eigenvalue ≤ 7 * κ := by
  rw [correctedMean_eq δ κ A hδ hκ,
    mul_nonneg_iff_of_pos_right (meanEnergy_pos A hA),
    le_div_iff₀ (by positivity : 0 < 56 * κ), zero_mul]
  exact sub_nonneg

theorem angularDissipation_eq_zero (A : ℝ) :
    weightedPalinstrophy (velocity A) - radialDissipation (velocity A) = 0 := by
  rw [radialDissipation_eq_weightedPalinstrophy, sub_self]

theorem projectionEnergy_pos (δ A : ℝ) (hA : 0 < A) :
    0 < weightedProjectionEnergy δ (velocity A) := by
  rw [projectionEnergy_eq_weightedPalinstrophy]
  have h := seven_mul_weightedPalinstrophy A
  have hp := mul_pos eigenvalue_pos (meanEnergy_pos A hA)
  linarith only [h, hp]

/-- Amplitude variation cannot be paid from angular dissipation alone. -/
theorem not_projectionEnergy_le_angularDissipation (δ A C : ℝ) (hA : 0 < A) :
    ¬ weightedProjectionEnergy δ (velocity A) ≤
      C * (weightedPalinstrophy (velocity A) - radialDissipation (velocity A)) := by
  rw [angularDissipation_eq_zero, mul_zero]
  exact not_le.mpr (projectionEnergy_pos δ A hA)

/-- The witness satisfies the actual unforced equation, with no hypothesized budget. -/
def heatSolution {ν : ℝ} (hν : 0 ≤ ν) (A T : ℝ) :
    LocalInfiniteVelocitySolution ν (velocity A) T
      (ParallelHeatFlow.initialSobolevEnergy (scalarData A)) :=
  ParallelHeatFlow.solution hν (scalarData A) (horizontal A)
    (fun q ↦ ParallelHeatFlow.sineCoefficients_reality wave q A)
    (ParallelHeatFlow.sineCoefficients_zero wave A) T

theorem coefficients_eq_decaying_amplitude (ν A t : ℝ) :
    ParallelHeatFlow.coefficients ν (scalarData A) t =
      velocity (A * Real.exp (-ν * eigenvalue * t)) := by
  funext q
  unfold ParallelHeatFlow.coefficients velocity
  congr 1
  by_cases hp : q = wave
  · subst q
    norm_num [scalarData, ParallelHeatFlow.sineCoefficients, ParallelHeatFlow.decayRate,
      wave, eigenvalue, Fin.sum_univ_three, Finsupp.single_apply,
      Matrix.vecCons_inj, Matrix.cons_val_two]
    ring
  · by_cases hn : q = -wave
    · subst q
      norm_num [scalarData, ParallelHeatFlow.sineCoefficients, ParallelHeatFlow.decayRate,
        wave, eigenvalue, Fin.sum_univ_three, Finsupp.single_apply,
        Matrix.vecCons_inj, Matrix.cons_val_two]
      ring
    · simp [scalarData, ParallelHeatFlow.sineCoefficients,
        Finsupp.single_eq_of_ne hp, Finsupp.single_eq_of_ne hn]

theorem heatSolution_coefficients {ν : ℝ} (hν : 0 ≤ ν) (A T t : ℝ) :
    (heatSolution hν A T).coefficients t = velocity (A * Real.exp (-ν * eigenvalue * t)) :=
  coefficients_eq_decaying_amplitude ν A t

theorem heatSolution_matched_correctedMean_neg {ν : ℝ} (hν : 0 ≤ ν)
    (δ A T t : ℝ) (hδ : 0 < δ) (hA : 0 < A) :
    meanCorrectedEnergy δ eigenvalue ((heatSolution hν A T).coefficients t) < 0 := by
  rw [heatSolution_coefficients]
  exact matched_correctedMean_neg δ _ hδ (mul_pos hA (Real.exp_pos _))

theorem heatSolution_stretching_eq_zero {ν : ℝ} (hν : 0 ≤ ν) (A T t : ℝ) :
    stretching ((heatSolution hν A T).coefficients t) = 0 := by
  rw [heatSolution_coefficients]
  exact ParallelHeatFlow.stretching_eq_zero _ (horizontal _)

/-- The amplitude-subtracted angular quantity passes the shear test. -/
theorem angularCurlEnergy_eq_zero (A : ℝ) :
    LocalAngularCurlBudget.angularCurlEnergy (velocity A) = 0 := by
  have h := LocalAngularCurlBudget.angularCurlEnergy_le (velocity A)
    (summable_fourierMoment modes _ (supported A) 3)
  rw [angularDissipation_eq_zero, mul_zero] at h
  exact le_antisymm h (LocalAngularCurlBudget.angularCurlEnergy_nonneg _)

theorem heatSolution_angularCurlEnergy_eq_zero {ν : ℝ} (hν : 0 ≤ ν) (A T t : ℝ) :
    LocalAngularCurlBudget.angularCurlEnergy ((heatSolution hν A T).coefficients t) = 0 := by
  rw [heatSolution_coefficients]
  exact angularCurlEnergy_eq_zero _

/-- The two costs are genuinely different on the same actual solution. -/
theorem heatSolution_angular_projection_separation {ν : ℝ} (hν : 0 ≤ ν)
    (δ A T t : ℝ) (hA : 0 < A) :
    LocalAngularCurlBudget.angularCurlEnergy ((heatSolution hν A T).coefficients t) = 0 ∧
      0 < weightedProjectionEnergy δ ((heatSolution hν A T).coefficients t) := by
  constructor
  · exact heatSolution_angularCurlEnergy_eq_zero hν A T t
  · rw [heatSolution_coefficients]
    exact projectionEnergy_pos δ _ (mul_pos hA (Real.exp_pos _))

end Mettapedia.FluidDynamics.NavierStokes.MonochromaticShearProjection
