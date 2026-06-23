import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePressureClosureBridge

/-!
# Core Regression Tests for Finite-Mode Spatial Reconstruction

This module checks the basic finite-mode reconstruction, pressure-gradient,
Helmholtz-range, and pressure-primitive-basis interfaces.
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

theorem finiteModeReconstructedVelocity_timeDerivative_at_regression
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime)
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (x : NSSpace) :
    timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x =
      finiteModeReconstructedAcceleration mode C a t x :=
  finiteModeReconstructedVelocity_timeDerivative_at mode C a t ha x

/-- Pressure modes reconstruct to the intended finite pressure sum. -/
theorem finiteModeReconstructedPressure_apply_regression
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedPressure pressureMode b t x =
      ∑ k : κ, b t k * pressureMode k x := by
  simp

/-- The reconstructed finite pressure gradient expands into modal gradients. -/
theorem finiteModeReconstructedPressure_spatialPressureGradient_regression
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace)
    (hmode : ∀ k, DifferentiableAt ℝ (pressureMode k) x) :
    spatialPressureGradient (finiteModeReconstructedPressure pressureMode b) t x =
      ∑ k : κ, b t k • gradient (pressureMode k) x :=
  finiteModeReconstructedPressure_spatialPressureGradient pressureMode b t x hmode

/-- The coordinate pressure ansatz realizes an arbitrary time-dependent constant
pressure gradient. -/
theorem finiteModeCoordinatePressure_spatialPressureGradient_regression
    (c : NSTime → NSSpace) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeCoordinatePressureMode
          (finiteModeCoordinatePressureCoefficients c)) t x =
      c t :=
  finiteModeCoordinatePressure_spatialPressureGradient c t x

/-- The diagonal quadratic pressure ansatz realizes nonconstant diagonal
linear-in-space pressure gradients. -/
theorem finiteModeDiagonalQuadraticPressure_spatialPressureGradient_regression
    (d : NSTime → FiniteModeState (Fin 3)) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
          (finiteModeDiagonalQuadraticPressureCoefficients d)) t x =
      ∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ)) :=
  finiteModeDiagonalQuadraticPressure_spatialPressureGradient d t x

/-- A finite pressure-mode gradient balance closes the reconstructed momentum
residual. -/
theorem finiteModeReconstructedMomentumResidualZeroOn_of_pressureModeGradient_balance_regression
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hbalance : ∀ t ∈ I, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            (∑ k : κ, b t k • gradient (pressureMode k) x) =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    finiteModeReconstructedMomentumResidualZeroOn I ν mode pressureMode C a b :=
  finiteModeReconstructedMomentumResidualZeroOn_of_pressureModeGradient_balance
    I ν mode pressureMode C a b hpressureModeDiff hbalance

theorem finiteModePressureHelmholtzRangeOn_iff_residualZeroOn_regression
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x) :
    (∃ b : ℝ → FiniteModeState κ,
        finiteModeReconstructedMomentumResidualZeroOn
          I ν mode pressureMode C a b) ↔
      ∀ t ∈ I,
        -finiteModeNonPressureMomentumDefect ν mode C a t ∈
          range (finiteModePressureGradientSynthesis pressureMode) :=
  finiteModePressureHelmholtzRangeOn_iff_residualZeroOn
    I ν mode pressureMode C a hpressureModeDiff

/-- A finite pressure-primitive basis realizes exactly its vector-field
subspace as a pressure-gradient range. -/
theorem finiteModePressureGradientSynthesis_range_eq_submodule_regression
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x) :
    range (finiteModePressureGradientSynthesis pressureMode) =
      (V : Set (NSSpace → NSSpace)) :=
  finiteModePressureGradientSynthesis_range_eq_submodule
    pressureMode V B hgradientBasis

/-- With a pressure-primitive basis, residual closure is equivalent to
membership of the non-pressure defect in the gradient subspace. -/
theorem finiteModePressurePrimitiveBasisOn_iff_residualZeroOn_regression
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x) :
    (∃ b : ℝ → FiniteModeState κ,
        finiteModeReconstructedMomentumResidualZeroOn
          I ν mode pressureMode C a b) ↔
      ∀ t ∈ I,
        -finiteModeNonPressureMomentumDefect ν mode C a t ∈ V :=
  finiteModePressurePrimitiveBasisOn_iff_residualZeroOn
    I ν mode pressureMode C a V B hpressureModeDiff hgradientBasis

end FiniteModeReconstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
