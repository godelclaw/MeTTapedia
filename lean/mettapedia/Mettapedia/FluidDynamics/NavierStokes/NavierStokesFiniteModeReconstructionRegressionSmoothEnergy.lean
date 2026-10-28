import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeReconstructionRegressionLinearExamples

/-!
# Smoothness and Energy Regression Tests for Finite-Mode Reconstruction

This module checks smooth polynomial evaluation surfaces and the bounded-energy
obstructions for active matrix-linear finite-mode fields.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped ContDiff
open scoped Laplacian

section FiniteModeReconstructionRegression

/-- Polynomial scalar evaluation is smooth on `NSSpace`. -/
theorem finiteModePolynomialEval_contDiff_top_regression
    (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (fun y : NSSpace => MvPolynomial.eval y p) :=
  finiteModePolynomialEval_contDiff_top p

/-- Polynomial vector fields are smooth on `NSSpace`. -/
theorem finiteModePolynomialVectorFieldEval_contDiff_top_regression
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (finiteModePolynomialVectorFieldEval U) :=
  finiteModePolynomialVectorFieldEval_contDiff_top U

/-- Smooth coefficient curves and smooth spatial modes reconstruct to a smooth
space-time velocity. -/
theorem finiteModeReconstructedVelocity_smoothSpaceTime_regression
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a : ℝ → FiniteModeState ι)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t : NSTime => a t i))
    (hmode : ∀ i, ContDiff ℝ ∞ (mode i)) :
    smoothSpaceTimeVelocity (finiteModeReconstructedVelocity mode a) :=
  finiteModeReconstructedVelocity_smoothSpaceTime mode a ha hmode

/-- Smooth pressure coefficient curves and smooth pressure modes reconstruct to
a smooth space-time pressure. -/
theorem finiteModeReconstructedPressure_smoothSpaceTime_regression
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (hb : ∀ k, ContDiff ℝ ∞ (fun t : NSTime => b t k))
    (hmode : ∀ k, ContDiff ℝ ∞ (pressureMode k)) :
    smoothSpaceTimePressure (finiteModeReconstructedPressure pressureMode b) :=
  finiteModeReconstructedPressure_smoothSpaceTime pressureMode b hb hmode

/-- Smooth amplitudes give smooth time-dependent matrix-linear velocities. -/
theorem finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity_regression
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) :
    smoothSpaceTimeVelocity (finiteModeLinearMatrixTimeVelocity A g) :=
  finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity A g hg

/-- Smooth amplitudes and derivative data give a smooth explicit pressure for
the time-dependent matrix-linear construction. -/
theorem finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure_regression
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot) :
    smoothSpaceTimePressure (finiteModeLinearMatrixTimePressure A g gdot) :=
  finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure A g gdot hg hgdot

/-- Smooth time-dependent matrix-linear finite-mode fields package smooth
regularity, pointwise momentum, and incompressibility. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_exists_regression
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot)
    (hderiv : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            smoothSpaceTimeVelocity u ∧
              smoothSpaceTimePressure p ∧
                (∀ t x,
                  timeVelocityDerivative u t x +
                      spatialConvection u t x +
                        spatialPressureGradient p t x =
                    ν • spatialLaplacian u t x) ∧
                ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_exists
    ν A g gdot hA htrace hg hgdot hderiv

/-- Linear-map kinetic-energy densities are continuous. -/
theorem finiteModeLinearMapKineticEnergyDensity_continuous_regression
    (L : NSSpace →L[ℝ] NSSpace) :
    Continuous (finiteModeLinearMapKineticEnergyDensity L) :=
  finiteModeLinearMapKineticEnergyDensity_continuous L

/-- Nonzero linear profiles have nonintegrable kinetic-energy density on
`ℝ^3`. -/
theorem not_integrable_finiteModeLinearMapKineticEnergyDensity_regression
    {L : NSSpace →L[ℝ] NSSpace}
    (hL : L ≠ 0) :
    ¬ MeasureTheory.Integrable (finiteModeLinearMapKineticEnergyDensity L) :=
  not_integrable_finiteModeLinearMapKineticEnergyDensity hL

/-- Matrix entries are exposed by the associated continuous linear map. -/
theorem finiteModeLinearMatrixCLM_apply_regression
    (A : Fin 3 → Fin 3 → ℝ) (x : NSSpace) (i : Fin 3) :
    finiteModeLinearMatrixCLM A x i = ∑ j : Fin 3, A i j * x j :=
  finiteModeLinearMatrixCLM_apply A x i

/-- A matrix with a nonzero entry gives a nonzero continuous linear map. -/
theorem finiteModeLinearMatrixCLM_ne_zero_of_entry_ne_regression
    {A : Fin 3 → Fin 3 → ℝ} {i j : Fin 3}
    (hA : A i j ≠ 0) :
    finiteModeLinearMatrixCLM A ≠ 0 :=
  finiteModeLinearMatrixCLM_ne_zero_of_entry_ne hA

/-- Time-dependent matrix-linear velocities have the expected component
formula. -/
theorem finiteModeLinearMatrixTimeVelocity_apply_regression
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeLinearMatrixTimeVelocity A g t x j =
      g t * ∑ k : Fin 3, A j k * x k :=
  finiteModeLinearMatrixTimeVelocity_apply A g t x j

/-- Time-slice kinetic energy for matrix-linear modes is the linear-map
kinetic-energy density of `(g(t))A`. -/
theorem kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity_regression
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) (t : NSTime) :
    kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t =
      finiteModeLinearMapKineticEnergyDensity ((g t) • finiteModeLinearMatrixCLM A) :=
  kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity A g t

/-- Active matrix-linear modes have nonintegrable kinetic-energy density on
active time slices. -/
theorem not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity_regression
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ} {t : NSTime}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg : g t ≠ 0) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t) :=
  not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity hA hg

/-- Genuinely active matrix-linear modes fail global bounded kinetic energy. -/
theorem not_boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity_regression
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg : ∃ t : NSTime, g t ≠ 0) :
    ¬ boundedKineticEnergy (finiteModeLinearMatrixTimeVelocity A g) :=
  not_boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity hA hg

/-- Active matrix-linear initial slices are not finite-energy admissible. -/
theorem not_finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial_regression
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg0 : g 0 ≠ 0) :
    ¬ finiteInitialKineticEnergy (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) :=
  not_finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial hA hg0

/-- Smooth matrix-linear PDE candidates with active modes package the precise
failure of the concrete bounded-energy predicate. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_without_boundedEnergy_exists_regression
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hAnz : ∃ i j : Fin 3, A i j ≠ 0)
    (hgnz : ∃ t : NSTime, g t ≠ 0)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot)
    (hderiv : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            smoothSpaceTimeVelocity u ∧
              smoothSpaceTimePressure p ∧
                (∀ t x,
                  timeVelocityDerivative u t x +
                      spatialConvection u t x +
                        spatialPressureGradient p t x =
                    ν • spatialLaplacian u t x) ∧
                (∀ t x, spatialDivergence u t x = 0) ∧
                  ¬ boundedKineticEnergy u :=
  finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_without_boundedEnergy_exists
    ν A g gdot hA htrace hAnz hgnz hg hgdot hderiv

end FiniteModeReconstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
