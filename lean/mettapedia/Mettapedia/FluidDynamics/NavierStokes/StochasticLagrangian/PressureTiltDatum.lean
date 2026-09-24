import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressurePairSum
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredPressure

/-!
# A smooth periodic datum for testing pressure tilt at pointwise alignment

The coefficients represent
`(2 sin(2πz) + ε(sin(4πy) - 2 sin(2πy)), 2 sin(2πx), 2 sin(2πy))`.
The perturbation preserves the first jet at the origin but changes the
pressure, which is evaluated from the existing Fourier Poisson operator.
This is a datum for the unforced equation, not a blowup construction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltDatum

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeFourierPressureStrain
open FourierPressurePairSum

def axisX : Wavevector := ![1, 0, 0]
def axisY : Wavevector := ![0, 1, 0]
def axisZ : Wavevector := ![0, 0, 1]
def doubleY : Wavevector := ![0, 2, 0]

def modes : Finset Wavevector := {axisX, -axisX, axisY, -axisY, axisZ, -axisZ, doubleY, -doubleY}

def velocity (epsilon : ℝ) (q : Wavevector) : VelocityCoefficient :=
  if q = axisX then ![0, -Complex.I, 0]
  else if q = -axisX then ![0, Complex.I, 0]
  else if q = axisY then ![(epsilon : ℂ) * Complex.I, 0, -Complex.I]
  else if q = -axisY then ![-(epsilon : ℂ) * Complex.I, 0, Complex.I]
  else if q = axisZ then ![-Complex.I, 0, 0]
  else if q = -axisZ then ![Complex.I, 0, 0]
  else if q = doubleY then ![-(epsilon : ℂ) * Complex.I / 2, 0, 0]
  else if q = -doubleY then ![(epsilon : ℂ) * Complex.I / 2, 0, 0]
  else 0

theorem velocity_eq_zero_of_not_mem (epsilon : ℝ) (q : Wavevector) (hq : q ∉ modes) :
    velocity epsilon q = 0 := by
  unfold velocity
  split_ifs <;> simp_all [modes]

theorem velocity_transverse (epsilon : ℝ) (q : Wavevector) :
    modeDot q (velocity epsilon q) = 0 := by
  unfold velocity
  split_ifs <;> simp_all [modeDot, axisX, axisY, axisZ, doubleY, Fin.sum_univ_three]

theorem modes_neg_closed (q : Wavevector) : -q ∈ modes ↔ q ∈ modes := by
  simp only [modes, Finset.mem_insert, Finset.mem_singleton, neg_eq_iff_eq_neg, neg_neg]
  tauto

theorem velocity_zero (epsilon : ℝ) : velocity epsilon 0 = 0 := by
  apply velocity_eq_zero_of_not_mem
  norm_num [modes, axisX, axisY, axisZ, doubleY, funext_iff, Fin.forall_fin_succ]

theorem velocity_conjugate (epsilon : ℝ) (q : Wavevector) :
    velocity epsilon (-q) = coefficientConjugate (velocity epsilon q) := by
  by_cases hq : q ∈ modes
  · simp only [modes, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq | hq | hq | hq | hq | hq <;> subst q <;>
      ext i <;> fin_cases i <;>
      norm_num [velocity, axisX, axisY, axisZ, doubleY, coefficientConjugate,
        funext_iff, Fin.forall_fin_succ, map_ofNat]
  · rw [velocity_eq_zero_of_not_mem epsilon q hq,
      velocity_eq_zero_of_not_mem epsilon (-q) (by simpa only [modes_neg_closed] using hq)]
    ext i
    simp [coefficientConjugate]

theorem sum_modes {E : Type*} [AddCommMonoid E] (f : Wavevector → E) :
    ∑ q ∈ modes, f q = f axisX + f (-axisX) + f axisY + f (-axisY) +
      f axisZ + f (-axisZ) + f doubleY + f (-doubleY) := by
  norm_num [modes, axisX, axisY, axisZ, doubleY, funext_iff, Fin.forall_fin_succ]
  abel

theorem velocity_values (epsilon : ℝ) :
    velocity epsilon axisX = ![0, -Complex.I, 0] ∧
    velocity epsilon (-axisX) = ![0, Complex.I, 0] ∧
    velocity epsilon axisY = ![(epsilon : ℂ) * Complex.I, 0, -Complex.I] ∧
    velocity epsilon (-axisY) = ![-(epsilon : ℂ) * Complex.I, 0, Complex.I] ∧
    velocity epsilon axisZ = ![-Complex.I, 0, 0] ∧
    velocity epsilon (-axisZ) = ![Complex.I, 0, 0] ∧
    velocity epsilon doubleY = ![-(epsilon : ℂ) * Complex.I / 2, 0, 0] ∧
    velocity epsilon (-doubleY) = ![(epsilon : ℂ) * Complex.I / 2, 0, 0] := by
  norm_num [velocity, axisX, axisY, axisZ, doubleY, funext_iff, Fin.forall_fin_succ]

def pressureFormula (epsilon : ℝ) (q : Wavevector) : ℂ :=
  -(epsilon : ℂ) *
    (outputIndicator q ![1, 1, 0] + outputIndicator q ![1, -1, 0] +
      outputIndicator q ![-1, 1, 0] + outputIndicator q ![-1, -1, 0]) +
    (2 * (epsilon : ℂ) / 5) *
      (outputIndicator q ![1, 2, 0] + outputIndicator q ![1, -2, 0] +
        outputIndicator q ![-1, 2, 0] + outputIndicator q ![-1, -2, 0])

set_option maxRecDepth 2048 in
set_option maxHeartbeats 300000 in
theorem pressureCoeff_eq (epsilon : ℝ) (q : Wavevector) :
    pressureCoeff modes (velocity epsilon) q = pressureFormula epsilon q := by
  obtain ⟨hX, hNX, hY, hNY, hZ, hNZ, hD, hND⟩ := velocity_values epsilon
  rw [pressureCoeff_eq_indicatorPairSum]
  simp only [sum_modes, orderedConvection, hX, hNX, hY, hNY, hZ, hNZ, hD, hND]
  norm_num [axisX, axisY, axisZ, doubleY, modeDot, modeSquare,
    Fin.sum_univ_three, pressureFormula, Matrix.cons_add_cons,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem infinitePressureCoeff_eq (epsilon : ℝ) (q : Wavevector) :
    PancakeInfinitePressureCoefficients.infinitePressureCoeff (velocity epsilon) q =
      pressureFormula epsilon q := by
  rw [InfiniteFilteredPressure.infinitePressureCoeff_eq_finite modes (velocity epsilon)
    (velocity_eq_zero_of_not_mem epsilon) (fun k _ ↦ velocity_transverse epsilon k)]
  exact pressureCoeff_eq epsilon q

def pressureModes : Finset Wavevector :=
  {![1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 0],
    ![1, 2, 0], ![1, -2, 0], ![-1, 2, 0], ![-1, -2, 0]}

theorem pressureFormula_eq_zero (epsilon : ℝ) (q : Wavevector) (hq : q ∉ pressureModes) :
    pressureFormula epsilon q = 0 := by
  simp_all [pressureModes, pressureFormula, outputIndicator, eq_comm]

theorem sum_pressureModes {E : Type*} [AddCommMonoid E] (f : Wavevector → E) :
    ∑ q ∈ pressureModes, f q =
      f ![1, 1, 0] + f ![1, -1, 0] + f ![-1, 1, 0] + f ![-1, -1, 0] +
      f ![1, 2, 0] + f ![1, -2, 0] + f ![-1, 2, 0] + f ![-1, -2, 0] := by
  norm_num [pressureModes, funext_iff, Fin.forall_fin_succ]
  abel

theorem pressureFormula_values (epsilon : ℝ) :
    pressureFormula epsilon ![1, 1, 0] = -(epsilon : ℂ) ∧
    pressureFormula epsilon ![1, -1, 0] = -(epsilon : ℂ) ∧
    pressureFormula epsilon ![-1, 1, 0] = -(epsilon : ℂ) ∧
    pressureFormula epsilon ![-1, -1, 0] = -(epsilon : ℂ) ∧
    pressureFormula epsilon ![1, 2, 0] = 2 * (epsilon : ℂ) / 5 ∧
    pressureFormula epsilon ![1, -2, 0] = 2 * (epsilon : ℂ) / 5 ∧
    pressureFormula epsilon ![-1, 2, 0] = 2 * (epsilon : ℂ) / 5 ∧
    pressureFormula epsilon ![-1, -2, 0] = 2 * (epsilon : ℂ) / 5 := by
  norm_num [pressureFormula, outputIndicator, funext_iff, Fin.forall_fin_succ]

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltDatum
