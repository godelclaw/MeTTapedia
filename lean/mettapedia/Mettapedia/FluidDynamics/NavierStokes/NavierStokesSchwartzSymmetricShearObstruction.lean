import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeLinearIncompressibleExamples
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDirectionalRigidity

/-!
# Symmetric-Shear Obstruction for the Nonzero Slice-Schwartz Canary

The symmetric off-diagonal shear finite-mode family is a useful laboratory
boundary case: it is nonzero, divergence-free, and closes the pointwise
momentum equation with affine-quadratic pressure.  This file proves that the
same linear-growth slice cannot inhabit the Schwartz initial-velocity lane.

The obstruction is derivative-level: the slice has a nonzero constant
directional derivative, while any constant-valued Schwartz derivative must have
zero constant value.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped ContDiff Laplacian LineDeriv SchwartzMap

/-- Universe-fixed unit index for the one-mode symmetric shear family. -/
def finiteModeSymmetricShearUnit : PUnit.{0} :=
  PUnit.unit

/-- The `e0` direction used to test the symmetric-shear derivative. -/
def finiteModeSymmetricShearDirection0 : NSSpace :=
  EuclideanSpace.single nsCoord0 (1 : ℝ)

theorem finiteModeSymmetricShearDirection0_ne_zero :
    finiteModeSymmetricShearDirection0 ≠ 0 := by
  intro h
  have hcoord := congrArg (fun x : NSSpace => x nsCoord0) h
  simp [finiteModeSymmetricShearDirection0, nsCoord0] at hcoord

/-- The derivative in the `e0` direction of the symmetric off-diagonal
polynomial shear is the constant vector `alpha e1`. -/
theorem finiteModeSymmetricShearPolynomialMode_fderiv_direction0
    (α : ℝ) (x : NSSpace) :
    fderiv ℝ
        (finiteModePolynomialVectorFieldEval
          (finiteModeSymmetricShearPolynomialMode α finiteModeSymmetricShearUnit)) x
        finiteModeSymmetricShearDirection0 =
      EuclideanSpace.single nsCoord1 α := by
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModeSymmetricShearPolynomialMode α finiteModeSymmetricShearUnit) x).fderiv]
  ext j
  fin_cases j <;>
    simp [finiteModeSymmetricShearDirection0,
      finiteModeSymmetricShearPolynomialMode,
      finiteModePolynomialVectorFieldFDeriv_apply,
      MvPolynomial.pderiv_X, MvPolynomial.eval_mul,
      nsCoord0, nsCoord1]

/-- A nonzero symmetric off-diagonal polynomial shear slice cannot be a
Schwartz initial velocity. -/
theorem
    not_exists_schwartzInitialVelocity_eq_finiteModeSymmetricShearPolynomialMode_of_alpha_ne_zero
    {α : ℝ} (hα : α ≠ 0) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) =
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α finiteModeSymmetricShearUnit) := by
  rintro ⟨u₀, hu₀⟩
  let d0 : 𝓢(NSSpace, NSSpace) :=
    ∂_{finiteModeSymmetricShearDirection0} u₀
  have hd0const :
      ∀ x : NSSpace, d0 x = EuclideanSpace.single nsCoord1 α := by
    intro x
    have hfun :
        (fun z : NSSpace => u₀ z) =
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α finiteModeSymmetricShearUnit) := by
      simpa using hu₀
    simp only [d0]
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change
      (fderiv ℝ (fun z : NSSpace => u₀ z) x) finiteModeSymmetricShearDirection0 =
        EuclideanSpace.single nsCoord1 α
    rw [hfun]
    exact finiteModeSymmetricShearPolynomialMode_fderiv_direction0 α x
  have hconstZero :
      EuclideanSpace.single nsCoord1 α = (0 : NSSpace) :=
    schwartzMap_constant_value_eq_zero d0
      finiteModeSymmetricShearDirection0_ne_zero hd0const
  have halpha : α = 0 := by
    have hcoord := congrArg (fun v : NSSpace => v nsCoord1) hconstZero
    simpa [nsCoord1] using hcoord
  exact hα halpha

/-- At time `1`, the reconstructed symmetric shear slice is the underlying
polynomial vector field. -/
theorem finiteModeSymmetricShear_reconstructedVelocity_one_eq_polynomialEval
    (α : ℝ) :
    (fun x : NSSpace =>
      finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α i) y)
        finiteModeIdentityCoefficientCurve 1 x) =
      finiteModePolynomialVectorFieldEval
        (finiteModeSymmetricShearPolynomialMode α finiteModeSymmetricShearUnit) := by
  funext x
  ext j
  fin_cases j <;>
    simp [finiteModeIdentityCoefficientCurve, finiteModeSymmetricShearPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply,
      MvPolynomial.eval_mul]

/-- The reconstructed symmetric off-diagonal finite-mode shear is nonzero when
its amplitude is nonzero. -/
theorem finiteModeSymmetricShear_reconstructedVelocity_nonzero_of_alpha_ne_zero
    {α : ℝ} (hα : α ≠ 0) :
    ∃ t x,
      finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeSymmetricShearPolynomialMode α i) y)
          finiteModeIdentityCoefficientCurve t x ≠ 0 := by
  refine ⟨1, EuclideanSpace.single nsCoord0 (1 : ℝ), ?_⟩
  intro hzero
  have hcoord := congrArg (fun v : NSSpace => v nsCoord1) hzero
  have hcomponent :
      finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeSymmetricShearPolynomialMode α i) y)
          finiteModeIdentityCoefficientCurve
          1 (EuclideanSpace.single nsCoord0 (1 : ℝ)) nsCoord1 = α := by
    simpa [nsCoord0, nsCoord1] using
      finiteModeSymmetricShear_reconstructedVelocity_apply
        α 1 (EuclideanSpace.single nsCoord0 (1 : ℝ)) nsCoord1
  have halpha : α = 0 := by
    have hcoord' :
        finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeSymmetricShearPolynomialMode α i) y)
            finiteModeIdentityCoefficientCurve
            1 (EuclideanSpace.single nsCoord0 (1 : ℝ)) nsCoord1 = 0 := by
      simpa using hcoord
    rw [hcomponent] at hcoord'
    exact hcoord'
  exact hα halpha

/-- The exact finite-mode symmetric shear is a genuine nonzero algebraic
pressure-closed canary, but its time-one slice is excluded from the
slice-Schwartz initial-velocity lane. -/
theorem finiteModeSymmetricShear_exact_nonzero_and_not_schwartzSlice
    (ν ε : ℝ) {α : ℝ} (hα : α ≠ 0) :
    (∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeSymmetricShearPolynomialMode α i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0) ∧
      (∃ t x,
        finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeSymmetricShearPolynomialMode α i) y)
            finiteModeIdentityCoefficientCurve t x ≠ 0) ∧
      ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) =
          fun x : NSSpace =>
            finiteModeReconstructedVelocity
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeSymmetricShearPolynomialMode α i) y)
              finiteModeIdentityCoefficientCurve 1 x := by
  refine ⟨finiteModeSymmetricShear_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
      ν ε α,
    finiteModeSymmetricShear_reconstructedVelocity_nonzero_of_alpha_ne_zero hα,
    ?_⟩
  rintro ⟨u₀, hu₀⟩
  exact
    not_exists_schwartzInitialVelocity_eq_finiteModeSymmetricShearPolynomialMode_of_alpha_ne_zero
      hα
      ⟨u₀,
        hu₀.trans
          (finiteModeSymmetricShear_reconstructedVelocity_one_eq_polynomialEval α)⟩

end NavierStokes
end FluidDynamics
end Mettapedia
