import Mettapedia.Analysis.FiniteResolventEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierCoordinateDerivatives

/-!
# Constructive smoothing of finite Fourier localizers

The resolvent uses integer frequencies. Physical derivative energies carry
the factors of `2 * pi` proved in `FourierCoordinateDerivatives`. Smoothing
preserves the exact coefficient support and controls second derivatives
and approximation error by the original first-derivative energy.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakeQuadraticFourierSupport
open FourierPressureCommutator FourierEllipticProductCoefficients FourierEllipticProductEnergy
open PancakeMisalignmentEnergyBridge FourierProductEnergy
open Mettapedia.Analysis.FiniteMultiplierLocalization
open Mettapedia.Analysis.FiniteResolventEnergy

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def smoothCutoff (epsilon : ℝ) (c : FourierCoeff (Fin 3)) : FourierCoeff (Fin 3) :=
  Finsupp.onFinset c.support (smooth epsilon (fun q ↦ ‖realFrequency q‖ ^ 2) c)
    (fun q hq ↦ Finsupp.mem_support_iff.mpr (fun hc ↦ hq (by simp [smooth, hc])))

@[simp]
theorem smoothCutoff_apply (epsilon : ℝ) (c : FourierCoeff (Fin 3)) (q : Wavevector) :
    smoothCutoff epsilon c q =
      smooth epsilon (fun k ↦ ‖realFrequency k‖ ^ 2) c q := rfl

theorem support_smoothCutoff (epsilon : ℝ) (he : 0 ≤ epsilon) (c : FourierCoeff (Fin 3)) :
    (smoothCutoff epsilon c).support = c.support := by
  ext q
  simp only [Finsupp.mem_support_iff, smoothCutoff_apply, smooth, ne_eq, mul_eq_zero,
    Complex.ofReal_eq_zero, ne_of_gt (multiplier_pos he (sq_nonneg ‖realFrequency q‖)),
    false_or]

@[simp]
theorem smoothCutoff_zero (c : FourierCoeff (Fin 3)) : smoothCutoff 0 c = c := by
  ext q
  simp [smooth, multiplier]

@[simp]
theorem smoothCutoff_apply_zero (epsilon : ℝ) (c : FourierCoeff (Fin 3)) :
    smoothCutoff epsilon c 0 = c 0 := by
  have hz : realFrequency 0 = 0 := by ext i; simp [realFrequency]
  simp [smooth, multiplier, hz]

/-- The inverse elliptic multiplier solves its coefficient equation
exactly, including at the zero frequency. -/
theorem resolvent_coefficient_identity (epsilon : ℝ) (he : 0 ≤ epsilon)
    (c : FourierCoeff (Fin 3)) (q : Wavevector) :
    smoothCutoff epsilon c q + (epsilon : ℂ) * laplaceMultiplier (smoothCutoff epsilon c) q = c q := by
  have hd : (1 + epsilon * ‖realFrequency q‖ ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hc : ((1 + epsilon * ‖realFrequency q‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [smoothCutoff_apply, smooth, multiplier, laplaceMultiplier,
    Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul] at hc ⊢
  field_simp

theorem coordinateEnergy_eq (P : Finset Wavevector) (c : Wavevector → ℂ) :
    coordinateEnergy P c = ∑ q ∈ P, ‖realFrequency q‖ ^ 2 * ‖c q‖ ^ 2 := by
  unfold coordinateEnergy scalarEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [coordinateMultiplier, norm_mul, mul_pow, Complex.norm_intCast,
    EuclideanSpace.norm_sq_eq, realFrequency,
    Real.norm_eq_abs, sq_abs, Finset.sum_mul]

theorem secondCoordinateEnergy_eq (P : Finset Wavevector) (c : Wavevector → ℂ) :
    secondCoordinateEnergy P c = ∑ q ∈ P, ‖realFrequency q‖ ^ 4 * ‖c q‖ ^ 2 := by
  unfold secondCoordinateEnergy scalarEnergy
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := P)]
  apply Finset.sum_congr rfl
  intro q _
  rw [show ‖realFrequency q‖ ^ 4 = (‖realFrequency q‖ ^ 2) ^ 2 by ring,
    EuclideanSpace.norm_sq_eq]
  simp only [secondCoordinateMultiplier, norm_mul, mul_pow, Complex.norm_intCast,
    realFrequency, Real.norm_eq_abs, sq_abs]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem coordinateEnergy_smooth_le (epsilon : ℝ) (he : 0 ≤ epsilon) (c : FourierCoeff (Fin 3)) :
    coordinateEnergy (smoothCutoff epsilon c).support (smoothCutoff epsilon c) ≤
      coordinateEnergy c.support c := by
  rw [support_smoothCutoff epsilon he, coordinateEnergy_eq, coordinateEnergy_eq]
  exact first_energy_smooth_le c.support epsilon he _ (fun q _ ↦ sq_nonneg _) c

theorem secondCoordinateEnergy_smooth_le (epsilon : ℝ) (he : 0 < epsilon) (c : FourierCoeff (Fin 3)) :
    secondCoordinateEnergy (smoothCutoff epsilon c).support (smoothCutoff epsilon c) ≤
      1 / (4 * epsilon) * coordinateEnergy c.support c := by
  rw [support_smoothCutoff epsilon he.le, secondCoordinateEnergy_eq, coordinateEnergy_eq]
  have h := second_energy_smooth_le c.support epsilon he (fun q ↦ ‖realFrequency q‖ ^ 2)
    (fun q _ ↦ sq_nonneg _) c
  simpa only [smoothCutoff_apply, ← pow_mul, Nat.reduceMul] using h

theorem error_energy_cutoff_le (epsilon : ℝ) (he : 0 ≤ epsilon) (c : FourierCoeff (Fin 3)) :
    scalarEnergy c.support (fun q ↦ c q - smoothCutoff epsilon c q) ≤
      epsilon / 4 * coordinateEnergy c.support c := by
  rw [coordinateEnergy_eq]
  exact error_energy_le c.support epsilon he _ (fun q _ ↦ sq_nonneg _) c

theorem integral_error_sq_eq (epsilon : ℝ) (he : 0 ≤ epsilon) (c : FourierCoeff (Fin 3)) :
    (∫ x : T3, ‖fourierPolynomial c x - fourierPolynomial (smoothCutoff epsilon c) x‖ ^ 2) =
      scalarEnergy c.support (fun q ↦ c q - smoothCutoff epsilon c q) := by
  have hid (x : T3) :
      fourierPolynomial c x - fourierPolynomial (smoothCutoff epsilon c) x =
        finiteScalarFourierReconstruction c.support (fun q ↦ c q - smoothCutoff epsilon c q) x := by
    rw [← PancakeQuadraticProjectionLocalization.scalarReconstruction_eq_fourierPolynomial,
      ← PancakeQuadraticProjectionLocalization.scalarReconstruction_eq_fourierPolynomial,
      support_smoothCutoff epsilon he]
    simp only [finiteScalarFourierReconstruction, mul_sub, Finset.sum_sub_distrib]
  simp_rw [hid]
  rw [← scalarEnergy_eq_integral]

theorem integral_error_sq_le (epsilon : ℝ) (he : 0 ≤ epsilon) (c : FourierCoeff (Fin 3)) :
    (∫ x : T3, ‖fourierPolynomial c x - fourierPolynomial (smoothCutoff epsilon c) x‖ ^ 2) ≤
      epsilon / 4 * coordinateEnergy c.support c := by
  rw [integral_error_sq_eq epsilon he c]
  exact error_energy_cutoff_le epsilon he c

end Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing
