import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredEquation

/-!
# Pressure correction in the exact filtered strain source

The resolved pressure and the pressure correction in the Leray-projected
subgrid force combine into the filtered pressure of the full velocity.
The unprojected subgrid force retains the complete infinite input fiber.
The identities hold at each output frequency, including frequency zero.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.InfiniteFilteredPressure

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeSobolevFiberEnvelope
open PancakeCoefficientLimitEquation PancakeInfinitePressureCoefficients
open PancakeFilteredStrainDynamics PancakePeriodicVorticityEquation
open PancakeFourierPressureStrain PancakeConvectionFiberIdentity
open PancakeFrequencyProjectorCommutator InfiniteFilteredEquation

def infinitePressureHessianCoeff (u : FourierVelocity) (q : Wavevector) : MatrixCoefficient :=
  fun i j ↦ unitTorusDerivativePhase ^ 2 * (q i : ℂ) * (q j : ℂ) * infinitePressureCoeff u q

/-- Before Leray projection, no input interaction has been discarded. -/
def rawSubgridForce (chi : Wavevector → ℂ) (u : FourierVelocity) (q : Wavevector) :
    VelocityCoefficient :=
  (-unitTorusDerivativePhase) • subgridConvection chi u q

theorem infinitePressureCoeff_eq_finite (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ modes → u k = 0) (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (q : Wavevector) : infinitePressureCoeff u q = pressureCoeff modes u q := by
  have hc : infiniteConvection u q = convectionConvolution modes u q := by
    ext i
    exact tsum_outputFiber_eq_convectionConvolution modes u hs hu q i
  simp only [infinitePressureCoeff, pressureCoeff, hc]

theorem infinitePressureHessianCoeff_eq_finite (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ modes → u k = 0) (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (q : Wavevector) : infinitePressureHessianCoeff u q = pressureHessianCoeff modes u q := by
  ext i j
  simp only [infinitePressureHessianCoeff, pressureHessianCoeff,
    infinitePressureCoeff_eq_finite modes u hs hu]

theorem strain_infinitePressureGradientCoeff (u : FourierVelocity) (q : Wavevector) :
    strainCoeff (infinitePressureGradientCoeff u) q = infinitePressureHessianCoeff u q := by
  ext i j
  simp only [strainCoeff, gradientCoeff, infinitePressureGradientCoeff,
    infinitePressureHessianCoeff, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

/-- The pressure correction is canceled jointly, before taking any norm. -/
theorem pressureGradient_subgridForce_balance
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ)
    (hchi : ∀ k, ‖chi k‖ ≤ C) (q : Wavevector)
    (hu : ∀ i, Summable (fun k ↦ outputFiber q u k i)) :
    -infinitePressureGradientCoeff (filteredVelocity chi u) q + subgridForce chi u q =
      -(chi q • infinitePressureGradientCoeff u q) + rawSubgridForce chi u q := by
  unfold rawSubgridForce
  have hp := filtered_infiniteVelocityRHS_pressure chi u C hchi 0 q hu
  have hl := filtered_infiniteVelocityRHS chi u C hchi 0 q hu
  rw [infiniteVelocityRHS_pressure_decomposition 0 (filteredVelocity chi u) q] at hl
  apply add_left_cancel (a := (-unitTorusDerivativePhase) •
    infiniteConvection (filteredVelocity chi u) q +
      unitTorusViscousVorticityCoeff 0 (filteredVelocity chi u) q)
  convert hl.symm.trans hp using 1 <;> abel

theorem pressureHessian_subgridStrain_balance
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ)
    (hchi : ∀ k, ‖chi k‖ ≤ C)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) (q : Wavevector) :
    -infinitePressureHessianCoeff (filteredVelocity chi u) q + strainCoeff (subgridForce chi u) q =
      -(chi q • infinitePressureHessianCoeff u q) + strainCoeff (rawSubgridForce chi u) q := by
  have hf : -infinitePressureGradientCoeff (filteredVelocity chi u) + subgridForce chi u =
      -filteredVelocity chi (infinitePressureGradientCoeff u) + rawSubgridForce chi u := by
    funext k
    exact pressureGradient_subgridForce_balance chi u C hchi k (hu k)
  have h := congrArg (fun v ↦ strainCoeff v q) hf
  simpa only [strainCoeff_add, strainCoeff_neg, strainCoeff_filtered,
    strain_infinitePressureGradientCoeff] using h

theorem resolvedPressure_subgridStrain_balance
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ)
    (hchi : ∀ k, ‖chi k‖ ≤ C) (modes : Finset Wavevector)
    (hs : ∀ k, k ∉ modes → chi k = 0) (hd : ∀ k, modeDot k (u k) = 0)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) (q : Wavevector) :
    -pressureHessianCoeff modes (filteredVelocity chi u) q + strainCoeff (subgridForce chi u) q =
      -(chi q • infinitePressureHessianCoeff u q) + strainCoeff (rawSubgridForce chi u) q := by
  rw [← infinitePressureHessianCoeff_eq_finite modes (filteredVelocity chi u)
    (fun k hk ↦ by simp [filteredVelocity, hs k hk])
    (fun k _ ↦ filteredVelocity_transverse chi u k (hd k))]
  exact pressureHessian_subgridStrain_balance chi u C hchi hu q

end Mettapedia.FluidDynamics.NavierStokes.InfiniteFilteredPressure
