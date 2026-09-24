import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeGalerkinVorticityBridge
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Pressure and velocity-gradient symbols for the physical finite equation

Pressure is constructed from the same convection convolution as the
velocity RHS. The gradient, symmetric strain and antisymmetric spin
coefficients keep every unit-torus derivative factor. Coefficient symmetry
means transpose symmetry, not complex self-adjointness; real symmetry is
obtained only after reconstructing a real field.

The material gradient equation below separates its matrix-square,
pressure-Hessian and viscous terms. It is a coefficient identity, not an
estimate of pressure or a solution-existence assertion.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFourierPressureStrain

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakeMaterialTransportCommutator PancakeFrequencyProjectorCommutator

abbrev MatrixCoefficient := Matrix (Fin 3) (Fin 3) ℂ
abbrev FourierMatrix := Wavevector → MatrixCoefficient

/-- `A_ij = partial_j u_i` in the physical unit-torus normalization. -/
def gradientCoeff (u : FourierVelocity) (q : Wavevector) : MatrixCoefficient :=
  fun i j ↦ unitTorusDerivativePhase * (q j : ℂ) * u q i

def strainCoeff (u : FourierVelocity) (q : Wavevector) : MatrixCoefficient :=
  (1 / 2 : ℂ) • (gradientCoeff u q + (gradientCoeff u q).transpose)

def spinCoeff (u : FourierVelocity) (q : Wavevector) : MatrixCoefficient :=
  (1 / 2 : ℂ) • (gradientCoeff u q - (gradientCoeff u q).transpose)

/-- Mean-zero pressure obtained by solving the Fourier divergence equation.
Division by zero returns zero, so the zero mode has the intended value. -/
def pressureCoeff (modes : Finset Wavevector) (u : FourierVelocity) (q : Wavevector) : ℂ :=
  -modeDot q (convectionConvolution modes u q) / modeSquare q

def pressureGradientCoeff (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) : VelocityCoefficient :=
  fun i ↦ unitTorusDerivativePhase * (q i : ℂ) * pressureCoeff modes u q

def pressureHessianCoeff (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) : MatrixCoefficient :=
  fun i j ↦ unitTorusDerivativePhase ^ 2 * (q i : ℂ) * (q j : ℂ) * pressureCoeff modes u q

def viscousGradientCoeff (nu : ℝ) (u : FourierVelocity) (q : Wavevector) : MatrixCoefficient :=
  ((nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) • gradientCoeff u q

theorem pressureCoeff_zero (modes : Finset Wavevector) (u : FourierVelocity) :
    pressureCoeff modes u 0 = 0 := by simp [pressureCoeff, modeDot]

theorem strainCoeff_add (u v : FourierVelocity) (q : Wavevector) :
    strainCoeff (u + v) q = strainCoeff u q + strainCoeff v q := by
  ext i j
  simp only [strainCoeff, gradientCoeff, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem strainCoeff_neg (u : FourierVelocity) (q : Wavevector) :
    strainCoeff (-u) q = -strainCoeff u q := by
  ext i j
  simp only [strainCoeff, gradientCoeff, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.neg_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem gradientCoeff_trace (u : FourierVelocity) (q : Wavevector) :
    (gradientCoeff u q).trace = unitTorusDerivativePhase * modeDot q (u q) := by
  simp only [Matrix.trace, Matrix.diag_apply, gradientCoeff, modeDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gradientCoeff_eq_strain_add_spin (u : FourierVelocity) (q : Wavevector) :
    gradientCoeff u q = strainCoeff u q + spinCoeff u q := by
  ext i j
  simp [strainCoeff, spinCoeff]
  ring

theorem strainCoeff_transpose (u : FourierVelocity) (q : Wavevector) :
    (strainCoeff u q).transpose = strainCoeff u q := by
  ext i j
  simp [strainCoeff, Matrix.transpose_apply]
  ring

theorem spinCoeff_transpose (u : FourierVelocity) (q : Wavevector) :
    (spinCoeff u q).transpose = -spinCoeff u q := by
  ext i j
  simp [spinCoeff, Matrix.transpose_apply]
  ring

theorem strainCoeff_trace_zero (u : FourierVelocity) (q : Wavevector)
    (hu : modeDot q (u q) = 0) : (strainCoeff u q).trace = 0 := by
  rw [strainCoeff, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_transpose,
    gradientCoeff_trace, hu]
  simp

theorem pressureHessianCoeff_symmetric (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) :
    (pressureHessianCoeff modes u q).transpose = pressureHessianCoeff modes u q := by
  ext i j
  simp only [Matrix.transpose_apply, pressureHessianCoeff]
  ring

theorem gradient_pressureGradientCoeff (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) :
    gradientCoeff (pressureGradientCoeff modes u) q = pressureHessianCoeff modes u q := by
  ext i j
  simp only [gradientCoeff, pressureGradientCoeff, pressureHessianCoeff]
  ring

theorem gradient_viscous (nu : ℝ) (u : FourierVelocity) (q : Wavevector) :
    gradientCoeff (unitTorusViscousVorticityCoeff nu u) q = viscousGradientCoeff nu u q := by
  ext i j
  simp [gradientCoeff, unitTorusViscousVorticityCoeff, viscousGradientCoeff]
  ring

theorem modeDot_add_wavevector (k l : Wavevector) (v : VelocityCoefficient) :
    modeDot (k + l) v = modeDot k v + modeDot l v := by
  simp [modeDot, add_mul, Finset.sum_add_distrib]

/-- The Fourier pressure really solves the Poisson equation associated with
the divergence of convection, including the zero mode. -/
theorem pressureCoeff_poisson (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) :
    modeSquare q * pressureCoeff modes u q = -modeDot q (convectionConvolution modes u q) := by
  by_cases hq : q = 0
  · subst q
    simp [modeDot, modeSquare]
  · have hs := modeSquare_ne_zero_of_frequencyVec_ne_zero (frequencyVec_ne_zero hq)
    unfold pressureCoeff
    field_simp

theorem pressureHessianCoeff_trace (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) :
    (pressureHessianCoeff modes u q).trace =
      -unitTorusDerivativePhase ^ 2 * modeDot q (convectionConvolution modes u q) := by
  have he : (pressureHessianCoeff modes u q).trace =
      unitTorusDerivativePhase ^ 2 * (modeSquare q * pressureCoeff modes u q) := by
    simp only [Matrix.trace, Matrix.diag_apply, pressureHessianCoeff,
      modeSquare, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, pressureCoeff_poisson]
  ring

/-- Exact pressure decomposition of the physical velocity equation, not a
separate momentum equation supplied as an assumption. -/
theorem velocityRHS_eq_negativeConvection_pressure_viscosity
    (modes : Finset Wavevector) (u : FourierVelocity) (nu : ℝ)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) (q : Wavevector) :
    velocityRHS modes u nu q =
      (-unitTorusDerivativePhase) • convectionConvolution modes u q -
        pressureGradientCoeff modes u q + unitTorusViscousVorticityCoeff nu u q := by
  rw [velocityRHS, finiteTransport_fourierCurl_eq modes u hk hu q, lerayMode_smul]
  by_cases hq : modeSquare q = 0
  · ext i
    simp [lerayMode, hq, pressureGradientCoeff, pressureCoeff]
  · ext i
    simp [lerayMode, hq, pressureGradientCoeff, pressureCoeff]
    ring

/-- Matrix product generated when the derivative lands on the advecting
velocity. The reverse pair order matches `partial_j u_m partial_m u_i`. -/
def gradientSquareCoeff (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) : MatrixCoefficient :=
  ∑ k ∈ modes, ∑ l ∈ modes,
    if k + l = q then gradientCoeff u l * gradientCoeff u k else 0

/-- Positive advection of the velocity-gradient matrix. -/
def gradientAdvectionCoeff (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) : MatrixCoefficient :=
  ∑ k ∈ modes, ∑ l ∈ modes,
    if k + l = q then
      (unitTorusDerivativePhase * modeDot l (u k)) • gradientCoeff u l else 0

theorem gradient_pair_product (u : FourierVelocity) (k l : Wavevector) (i j : Fin 3) :
    (gradientCoeff u l * gradientCoeff u k) i j =
      unitTorusDerivativePhase ^ 2 * (k j : ℂ) * modeDot l (u k) * u l i := by
  simp only [Matrix.mul_apply, gradientCoeff, modeDot, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The product rule for convection, at each ordered Fourier interaction. -/
theorem gradient_convection_pair (u : FourierVelocity) (k l : Wavevector) (i j : Fin 3) :
    unitTorusDerivativePhase * ((k + l) j : ℂ) *
        ((-unitTorusDerivativePhase) * (orderedConvection k l u i)) +
      ((unitTorusDerivativePhase * modeDot l (u k)) • gradientCoeff u l) i j =
        -(gradientCoeff u l * gradientCoeff u k) i j := by
  rw [gradient_pair_product]
  simp [gradientCoeff, orderedConvection]
  ring

theorem gradient_negativeConvection_add_advection
    (modes : Finset Wavevector) (u : FourierVelocity) (q : Wavevector) :
    gradientCoeff (fun k ↦ (-unitTorusDerivativePhase) • convectionConvolution modes u k) q +
      gradientAdvectionCoeff modes u q = -gradientSquareCoeff modes u q := by
  classical
  ext i j
  simp only [gradientCoeff, convectionConvolution, Pi.smul_apply, smul_eq_mul,
    gradientAdvectionCoeff, gradientSquareCoeff, Matrix.add_apply, Matrix.neg_apply,
    Matrix.sum_apply, Finset.sum_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hkl : k + l = q
  · subst q
    simpa only [ite_true]
      using gradient_convection_pair u k l i j
  · simp [hkl]

/-- Full material gradient coefficient identity with all three physical
channels explicit. -/
theorem gradient_velocityRHS_material (modes : Finset Wavevector) (u : FourierVelocity)
    (nu : ℝ) (q : Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    gradientCoeff (velocityRHS modes u nu) q + gradientAdvectionCoeff modes u q =
      -gradientSquareCoeff modes u q - pressureHessianCoeff modes u q +
        viscousGradientCoeff nu u q := by
  have hgrad : gradientCoeff (velocityRHS modes u nu) q =
      gradientCoeff (fun k ↦ (-unitTorusDerivativePhase) • convectionConvolution modes u k) q -
        pressureHessianCoeff modes u q + viscousGradientCoeff nu u q := by
    rw [← gradient_pressureGradientCoeff, ← gradient_viscous]
    ext i j
    rw [gradientCoeff, velocityRHS_eq_negativeConvection_pressure_viscosity modes u nu hk hu q]
    simp [gradientCoeff]
    ring
  rw [hgrad]
  have he := gradient_negativeConvection_add_advection modes u q
  calc
    _ = (gradientCoeff (fun k ↦ (-unitTorusDerivativePhase) • convectionConvolution modes u k) q +
        gradientAdvectionCoeff modes u q) - pressureHessianCoeff modes u q +
          viscousGradientCoeff nu u q := by abel
    _ = _ := by rw [he]

theorem hasDerivAt_gradientCoeff (u : ℝ → FourierVelocity) (du : FourierVelocity)
    (q : Wavevector) (i j : Fin 3) (t : ℝ)
    (hd : HasDerivAt (fun tau ↦ u tau q i) (du q i) t) :
    HasDerivAt (fun tau ↦ gradientCoeff (u tau) q i j) (gradientCoeff du q i j) t :=
  hd.const_mul (unitTorusDerivativePhase * (q j : ℂ))

end Mettapedia.FluidDynamics.NavierStokes.PancakeFourierPressureStrain
