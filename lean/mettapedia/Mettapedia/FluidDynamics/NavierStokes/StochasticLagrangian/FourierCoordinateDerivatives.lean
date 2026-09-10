import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierEllipticProductEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierTranslationCurve

/-!
# Physical derivatives behind the coordinate multiplier energies

The first derivative has one unit-torus phase factor and the mixed
second derivative has two. Parseval gives the corresponding squared
phase factors in the derivative energies. No regularity assumptions
are needed for these finite polynomials.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierCoordinateDerivatives

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakePeriodicVorticityEquation
open PancakeMisalignmentEnergyBridge PancakeFourierTranslationCurve
open PancakeHaarTransportRate
open FourierEllipticProductCoefficients FourierProductEnergy
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fourierField_apply_eq (P : Finset Wavevector) (c : Wavevector → ℂ) (x : T3) :
    fourierField P c x = finiteScalarFourierReconstruction P c x := by
  simp only [fourierField, modeField, ContinuousMap.sum_apply, ContinuousMap.coe_mk,
    smul_eq_mul, finiteScalarFourierReconstruction]

theorem reconstruction_derivativeCoeff (P : Finset Wavevector) (c : Wavevector → ℂ)
    (j : Fin 3) (x : T3) :
    finiteScalarFourierReconstruction P (derivativeCoeff j c) x =
      unitTorusDerivativePhase * finiteScalarFourierReconstruction P (coordinateMultiplier c j) x := by
  simp only [finiteScalarFourierReconstruction, derivativeCoeff, coordinateMultiplier,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem hasDerivAt_reconstruction_shift (P : Finset Wavevector) (c : Wavevector → ℂ)
    (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t : ℝ ↦ finiteScalarFourierReconstruction P c (x + coordinateShift j t))
      (unitTorusDerivativePhase * finiteScalarFourierReconstruction P (coordinateMultiplier c j)
        (x + coordinateShift j h)) h := by
  have he := (ContinuousMap.evalCLM (R := ℝ) (M := ℂ) x).hasFDerivAt.comp_hasDerivAt h
    (hasDerivAt_translationCurve P c j h)
  change HasDerivAt (fun t ↦ translationCurve P c j t x)
    (translationCurve P (derivativeCoeff j c) j h x) h at he
  simpa only [translationCurve_apply, fourierField_apply_eq, reconstruction_derivativeCoeff] using he

def polynomialDerivative (P : Finset Wavevector) (c : Wavevector → ℂ) (j : Fin 3) (x : T3) : ℂ :=
  deriv (fun t : ℝ ↦ finiteScalarFourierReconstruction P c (x + coordinateShift j t)) 0

theorem polynomialDerivative_eq (P : Finset Wavevector) (c : Wavevector → ℂ)
    (j : Fin 3) (x : T3) : polynomialDerivative P c j x =
      unitTorusDerivativePhase * finiteScalarFourierReconstruction P (coordinateMultiplier c j) x := by
  simpa only [polynomialDerivative, coordinateShift_zero, add_zero] using
    (hasDerivAt_reconstruction_shift P c j x 0).deriv

theorem hasDerivAt_polynomialDerivative_shift (P : Finset Wavevector) (c : Wavevector → ℂ)
    (i j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t : ℝ ↦ polynomialDerivative P c j (x + coordinateShift i t))
      (unitTorusDerivativePhase ^ 2 * finiteScalarFourierReconstruction P (secondCoordinateMultiplier c i j)
        (x + coordinateShift i h)) h := by
  have hD := (hasDerivAt_reconstruction_shift P (coordinateMultiplier c j) i x h).const_mul unitTorusDerivativePhase
  have hc : coordinateMultiplier (coordinateMultiplier c j) i = secondCoordinateMultiplier c i j := by
    funext q
    simp only [coordinateMultiplier, secondCoordinateMultiplier]
    ring
  simp only [hc, ← mul_assoc, ← sq] at hD
  simpa only [polynomialDerivative_eq] using hD

theorem integral_polynomialDerivative_sq (P : Finset Wavevector) (c : Wavevector → ℂ) (j : Fin 3) :
    (∫ x : T3, ‖polynomialDerivative P c j x‖ ^ 2) =
      ‖unitTorusDerivativePhase‖ ^ 2 * scalarEnergy P (coordinateMultiplier c j) := by
  simp_rw [polynomialDerivative_eq, norm_mul, mul_pow]
  rw [integral_const_mul, ← scalarEnergy_eq_integral]

theorem integral_second_polynomialDerivative_sq (P : Finset Wavevector) (c : Wavevector → ℂ)
    (i j : Fin 3) :
    (∫ x : T3, ‖deriv (fun t : ℝ ↦ polynomialDerivative P c j (x + coordinateShift i t)) 0‖ ^ 2) =
      ‖unitTorusDerivativePhase‖ ^ 4 * scalarEnergy P (secondCoordinateMultiplier c i j) := by
  have hd (x : T3) := (hasDerivAt_polynomialDerivative_shift P c i j x 0).deriv
  simp only [coordinateShift_zero, add_zero] at hd
  simp_rw [hd, norm_mul, norm_pow, mul_pow, ← pow_mul]
  rw [integral_const_mul, ← scalarEnergy_eq_integral]

end Mettapedia.FluidDynamics.NavierStokes.FourierCoordinateDerivatives
