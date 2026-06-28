import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzSymmetricShearObstruction

/-!
# Regression checks for the symmetric-shear Schwartz obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped ContDiff Laplacian LineDeriv SchwartzMap

namespace Regression

theorem symmetricShear_polynomial_direction0_derivative_regression
    (α : ℝ) (x : NSSpace) :
    fderiv ℝ
        (finiteModePolynomialVectorFieldEval
          (finiteModeSymmetricShearPolynomialMode α finiteModeSymmetricShearUnit)) x
        finiteModeSymmetricShearDirection0 =
      EuclideanSpace.single nsCoord1 α := by
  exact finiteModeSymmetricShearPolynomialMode_fderiv_direction0 α x

theorem symmetricShear_nonzero_reconstruction_regression
    {α : ℝ} (hα : α ≠ 0) :
    ∃ t x,
      finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeSymmetricShearPolynomialMode α i) y)
          finiteModeIdentityCoefficientCurve t x ≠ 0 := by
  exact finiteModeSymmetricShear_reconstructedVelocity_nonzero_of_alpha_ne_zero hα

theorem symmetricShear_not_schwartz_slice_regression
    {α : ℝ} (hα : α ≠ 0) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) =
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α finiteModeSymmetricShearUnit) := by
  exact
    not_exists_schwartzInitialVelocity_eq_finiteModeSymmetricShearPolynomialMode_of_alpha_ne_zero
      hα

theorem symmetricShear_exact_nonzero_and_not_schwartz_regression
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
  exact finiteModeSymmetricShear_exact_nonzero_and_not_schwartzSlice ν ε hα

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
