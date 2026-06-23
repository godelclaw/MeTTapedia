import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeReconstructionRegressionObstructions
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeUniformAccelerationExample
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeLocalExistence
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressureMomentumClosure

/-!
# Local Momentum Regression Tests for Finite-Mode Reconstruction

This module checks local reconstructed velocity/pressure momentum surfaces,
including polynomial Helmholtz and curl-free closure variants.
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

/-- The uniform-acceleration finite-mode reconstruction has zero momentum
residual on all time. -/
theorem finiteModeUniformAcceleration_reconstructedResidualZeroOn_univ_regression
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      finiteModeUniformAccelerationMode finiteModeCoordinatePressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeUniformAccelerationPressureCoefficients :=
  finiteModeUniformAcceleration_reconstructedResidualZeroOn_univ ν

/-- The uniform-acceleration mode gives an explicit reconstructed velocity and
pressure satisfying the pointwise momentum equation. -/
theorem finiteModeUniformAcceleration_reconstructed_velocityPressure_momentum_exists_regression
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeUniformAccelerationPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x :=
  finiteModeUniformAcceleration_reconstructed_velocityPressure_momentum_exists ν

/-- Zero reconstructed residual is exactly the pointwise momentum equation once
the coefficient curve solves the projected ODE. -/
theorem finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at_regression
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (t : NSTime)
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (x : NSSpace) :
    finiteModeReconstructedMomentumResidualZeroAt
        ν mode pressureMode C a b t x ↔
      timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            spatialPressureGradient
              (finiteModeReconstructedPressure pressureMode b) t x =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x :=
  finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
    ν mode pressureMode C a b t ha x

/-- Picard's one-mode coefficient solution reconstructs to an actual concrete
velocity field with the local projected-RHS derivative identity. -/
theorem oneModeProjectedNS_local_reconstructed_velocity_regression
    (mode : PUnit → NSSpace → NSSpace)
    (c₀ c₁ c₂ a₀ : ℝ) :
    ∃ a : ℝ → FiniteModeState PUnit, ∃ u : NSVelocityField,
      a 0 = (fun _ : PUnit => a₀) ∧
        u 0 =
          finiteModeReconstructedInitialVelocity mode (fun _ : PUnit => a₀) ∧
          ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x =
              finiteModeReconstructedAcceleration mode
                ({ forcing := fun _ => c₀
                   linear := fun _ _ => c₁
                   quadratic := fun _ _ _ => c₂ } :
                  FiniteModeProjectedNSCoefficients PUnit) a t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocity_exists mode
      ({ forcing := fun _ => c₀
         linear := fun _ _ => c₁
         quadratic := fun _ _ _ => c₂ } :
        FiniteModeProjectedNSCoefficients PUnit)
      (fun _ => a₀)

/-- Divergence-free modes reconstruct to a divergence-free velocity field. -/
theorem finiteModeReconstructedVelocity_spatialDivergence_zero_regression
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (a : ℝ → FiniteModeState ι)
    (hmodeDiff : ∀ i x, DifferentiableAt ℝ (mode i) x)
    (hmodeDiv : ∀ i t x, spatialDivergence (fun _ : NSTime => mode i) t x = 0)
    (t : NSTime) (x : NSSpace) :
    spatialDivergence (finiteModeReconstructedVelocity mode a) t x = 0 :=
  finiteModeReconstructedVelocity_spatialDivergence_zero
    mode a hmodeDiff hmodeDiv t x

/-- The one-mode Picard reconstruction can carry incompressibility when the
chosen mode is divergence-free. -/
theorem oneModeProjectedNS_local_reconstructed_divergenceFree_velocity_regression
    (mode : PUnit → NSSpace → NSSpace)
    (c₀ c₁ c₂ a₀ : ℝ)
    (hmodeDiff : ∀ i x, DifferentiableAt ℝ (mode i) x)
    (hmodeDiv : ∀ i t x, spatialDivergence (fun _ : NSTime => mode i) t x = 0) :
    ∃ a : ℝ → FiniteModeState PUnit, ∃ u : NSVelocityField,
      a 0 = (fun _ : PUnit => a₀) ∧
        u 0 =
          finiteModeReconstructedInitialVelocity mode (fun _ : PUnit => a₀) ∧
          ∃ ε > (0 : ℝ),
            (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
              timeVelocityDerivative u t x =
                finiteModeReconstructedAcceleration mode
                  ({ forcing := fun _ => c₀
                     linear := fun _ _ => c₁
                     quadratic := fun _ _ _ => c₂ } :
                    FiniteModeProjectedNSCoefficients PUnit) a t x) ∧
            (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace, spatialDivergence u t x = 0) := by
  exact
    finiteModeProjectedNS_local_reconstructed_divergenceFree_velocity_exists mode
      ({ forcing := fun _ => c₀
         linear := fun _ _ => c₁
         quadratic := fun _ _ _ => c₂ } :
        FiniteModeProjectedNSCoefficients PUnit)
      (fun _ => a₀) hmodeDiff hmodeDiv

/-- A one-mode coefficient solution plus explicit zero residual reconstructs
to a concrete velocity-pressure pair satisfying pointwise momentum locally. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPressure_momentum_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (pressureMode : PUnit → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (b : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hres :
      finiteModeReconstructedMomentumResidualZeroOn
        (Ioo (-ε) ε) ν mode pressureMode C a b) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_residual_zero
    ν mode pressureMode C a b ε ha hres

/-- A one-mode coefficient solution plus a Helmholtz range witness constructs
pressure coefficients and reconstructs local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureHelmholtzRange_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (pressureMode : PUnit → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hrange : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t ∈
        range (finiteModePressureGradientSynthesis pressureMode)) :
    ∃ b : ℝ → FiniteModeState PUnit, ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode pressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureHelmholtzRange
    ν mode pressureMode C a ε ha hpressureModeDiff hrange

/-- A local coefficient ODE solution plus a pressure-primitive basis and
subspace-valued defect reconstructs local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressurePrimitiveBasis_regression
    {κ : Type*} [Fintype κ]
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x)
    (hdefectV : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t ∈ V) :
    ∃ b : ℝ → FiniteModeState κ, ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode pressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressurePrimitiveBasis
    ν mode pressureMode C a ε ha V B hpressureModeDiff hgradientBasis hdefectV

/-- A one-mode coefficient solution whose non-pressure defect is a curl-free
polynomial vector field constructs the corresponding time-dependent polynomial
pressure primitive and reconstructs local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialHelmholtz_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i))
    (hdefect : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = (fun t x => finiteModePolynomialPressureMode (G t) x) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialHelmholtz
    ν mode C a ε ha G hcurl hdefect

/-- For one-mode reconstructions, polynomial-pressure solvability of the local
momentum equation is equivalent to curl-freeness of the polynomial defect. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialDefect_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hdefect : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
          timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
              spatialConvection (finiteModeReconstructedVelocity mode a) t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) ↔
      ∀ t ∈ Ioo (-ε) ε, ∀ i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialDefect
    ν mode C a ε ha G hdefect

/-- For polynomial one-mode spatial modes with a polynomial Laplacian
representation, local polynomial-pressure solvability is exactly curl-freeness
of the explicit closing pressure-gradient polynomial. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_laplacian_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (lapPoly : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hLap : ∀ t x,
      spatialLaplacian
          (finiteModeReconstructedVelocity
            (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
        finiteModePolynomialVectorFieldEval (lapPoly t) x) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
          timeVelocityDerivative
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
              spatialConvection
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            ν • spatialLaplacian
              (finiteModeReconstructedVelocity
                (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
              t x) ↔
      ∀ t ∈ Ioo (-ε) ε, ∀ i j,
        MvPolynomial.pderiv i
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a lapPoly t j) =
          MvPolynomial.pderiv j
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a lapPoly t i) :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_laplacian
    ν modePoly C a ε ha lapPoly hLap

/-- For polynomial one-mode spatial modes, local polynomial-pressure
solvability is exactly curl-freeness of the closing pressure-gradient
polynomial built with the formal Laplacian. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
          timeVelocityDerivative
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
              spatialConvection
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            ν • spatialLaplacian
              (finiteModeReconstructedVelocity
                (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
              t x) ↔
      ∀ t ∈ Ioo (-ε) ε, ∀ i j,
        MvPolynomial.pderiv i
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
              t j) =
          MvPolynomial.pderiv j
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
              t i) :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes
    ν modePoly C a ε ha

/-- Positive polynomial-mode closure: curl-freeness of the computed closing
gradient constructs the explicit polynomial pressure primitive and closes
local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialModes_curlFree_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hcurl : ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      MvPolynomial.pderiv i
          (finiteModePolynomialClosingPressureGradientComponents
            ν modePoly C a
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
            t j) =
        MvPolynomial.pderiv j
          (finiteModePolynomialClosingPressureGradientComponents
            ν modePoly C a
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
            t i)) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a ∧
        p = (fun t x =>
          finiteModePolynomialPressureMode
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
              t) x) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialModes_curlFree
    ν modePoly C a ε ha hcurl

end FiniteModeReconstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
