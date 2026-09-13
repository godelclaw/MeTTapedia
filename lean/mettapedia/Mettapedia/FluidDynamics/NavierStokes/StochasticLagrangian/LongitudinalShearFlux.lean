import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalGradientFlux
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MonochromaticShearEvolution

/-!
# Strict joint-flux improvement on an exact unforced shear

The raw joint-flux square is positive for a nonzero viscous monochromatic
shear, but its gradient projection vanishes. The cancellation holds along
the exact decaying infinite Fourier solution, not just independent jets.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalShearFlux

open scoped RealInnerProductSpace Topology
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeFourierTranslationCurve PancakePeriodicVorticityEquation
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalAlignmentForcing
open LongitudinalJointFlux LongitudinalGradientFlux MonochromaticShearProjection FourierFiniteSupport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem flux_eq (ν A : ℝ) (j : Fin 3) (x : T3) :
    flux ν (velocity A) j x = if j = 1 then
      (2 * ν * (eigenvalue * A * sine x) ^ 2) • EuclideanSpace.single 1 (1 : ℝ) else 0 := by
  have hs := ParallelHeatFlow.fullStrain_apply_vorticity_eq_zero (scalarData A) (horizontal A) x
  change fullStrainOperator (velocity A) x (fullVorticity (velocity A) x) = 0 at hs
  simp only [flux, hs, smul_zero, neg_zero, zero_add]
  simp_rw [vorticityGradient_eq]
  fin_cases j <;> ext i <;> fin_cases i <;>
    norm_num [Fin.sum_univ_three, PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply]
  all_goals ring_nf
  all_goals simp

theorem sine_shift_one (x : T3) (t : ℝ) : sine (x + coordinateShift 1 t) = sine x := by
  simp [sine, mFourier_space_add, mFourier_coordinateShift, wave]

theorem flux_diagonal_shift (ν A : ℝ) (j : Fin 3) (x : T3) (t : ℝ) :
    flux ν (velocity A) j (x + coordinateShift j t) = flux ν (velocity A) j x := by
  rw [flux_eq, flux_eq]
  by_cases hj : j = 1
  · subst j
    rw [sine_shift_one]
  · simp only [hj, if_false]

theorem projectedFlux_eq_zero (ν A : ℝ) : projectedFlux ν (velocity A) = 0 := by
  have hu := summable_fourierMoment modes (velocity A) (supported A) 1
  apply gradientProjection_eq_zero_of_divergence_zero (fluxField ν (velocity A)) (fun _ ↦ 0)
  · intro j x h
    have hshift : UnitTorusWeakDerivative.coordinateShift j = coordinateShift j := rfl
    simp only [hshift, fluxField_apply ν _ hu, ContinuousMap.zero_apply]
    simpa only [flux_diagonal_shift] using hasDerivAt_const h (flux ν (velocity A) j x)
  · intro x
    simp

theorem projectedFluxSquare_eq_zero (ν A : ℝ) : projectedFluxSquare ν (velocity A) = 0 := by
  simp [projectedFluxSquare, projectedFlux_eq_zero]

theorem sine_quarter : sine (coordinateShift 0 (1 / 4)) = 1 := by
  rw [sine, mFourier_coordinateShift]
  have he : unitTorusDerivativePhase * (wave 0 : ℂ) * ((1 / 4 : ℝ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    simp [unitTorusDerivativePhase, wave]
    ring
  rw [he, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two]

theorem fluxSquare_pos (ν A : ℝ) (hν : 0 < ν) (hA : 0 < A) : 0 < fluxSquare ν (velocity A) := by
  have hu := summable_fourierMoment modes (velocity A) (supported A) 1
  have hc : Continuous (fun x : T3 ↦ ∑ j, ‖flux ν (velocity A) j x‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ ↦ (continuous_flux ν _ hu j).norm.pow 2)
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun x ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  show (∑ j, ‖flux ν (velocity A) j (coordinateShift 0 (1 / 4))‖ ^ 2) ≠ 0
  simp only [flux_eq, sine_quarter]
  simp [Fin.sum_univ_three, norm_smul, PiLp.norm_single,
    ne_of_gt hν, ne_of_gt hA, ne_of_gt eigenvalue_pos]

theorem not_fluxSquare_le_projected (ν A C : ℝ) (hν : 0 < ν) (hA : 0 < A) :
    ¬ fluxSquare ν (velocity A) ≤ C * projectedFluxSquare ν (velocity A) := by
  rw [projectedFluxSquare_eq_zero, mul_zero]
  exact not_le.mpr (fluxSquare_pos ν A hν hA)

theorem heatSolution_flux_separation {ν : ℝ} (hν : 0 < ν) (A T t : ℝ) (hA : 0 < A) :
    projectedFluxSquare ν ((heatSolution hν.le A T).coefficients t) = 0 ∧
      0 < fluxSquare ν ((heatSolution hν.le A T).coefficients t) := by
  rw [heatSolution_coefficients]
  exact ⟨projectedFluxSquare_eq_zero ν _, fluxSquare_pos ν _ hν (mul_pos hA (Real.exp_pos _))⟩

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalShearFlux
