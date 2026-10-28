import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressureMomentumClosure

/-!
# Radial-linear finite-mode examples and explicit affine-quadratic pressure closure.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped BigOperators
open scoped ContDiff
open scoped Laplacian

/-- One-mode polynomial spatial mode `x ↦ x`.  This gives a concrete
nonconstant finite-mode reconstruction whose pressure closure is handled by
the general polynomial primitive theorem. -/
def finiteModeRadialLinearPolynomialMode (_ : PUnit) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => MvPolynomial.X j

/-- The radial linear reconstruction is the concrete field `u(t,x)=t x`. -/
theorem finiteModeRadialLinear_reconstructedVelocity_eq
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve t x =
      t • x := by
  ext j
  simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
    finiteModeRadialLinearPolynomialMode, finiteModeIdentityCoefficientCurve,
    finiteModePolynomialVectorFieldEval_apply]

/-- The projected acceleration for the radial linear identity-coefficient
solution is `x`. -/
theorem finiteModeRadialLinear_reconstructedAcceleration_eq
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      x := by
  ext j
  simp [finiteModeReconstructedAcceleration, finiteModeReconstructedVelocity,
    finiteModeReconstructionCLM, finiteModeProjectedNSRHS,
    finiteModeUnitForcingCoefficients, finiteModeIdentityCoefficientCurve,
    finiteModeRadialLinearPolynomialMode, finiteModePolynomialVectorFieldEval_apply]

/-- The time derivative of the radial linear reconstruction is `x`. -/
theorem finiteModeRadialLinear_timeVelocityDerivative_eq
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      x := by
  rw [finiteModeReconstructedVelocity_timeDerivative_at
    (fun i y => finiteModePolynomialVectorFieldEval
      (finiteModeRadialLinearPolynomialMode i) y)
    finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t
    (finiteModeIdentityCoefficientCurve_hasDerivAt t) x]
  exact finiteModeRadialLinear_reconstructedAcceleration_eq t x

/-- The convection term for `u(t,x)=t x` is `t^2 x`. -/
theorem finiteModeRadialLinear_spatialConvection_eq
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      (t * t) • x := by
  rw [finiteModePolynomialReconstructedVelocity_spatialConvection
    finiteModeRadialLinearPolynomialMode finiteModeIdentityCoefficientCurve t x]
  ext j
  simp [finiteModePolynomialConvectionComponents,
    finiteModePolynomialReconstructedVelocityComponents,
    finiteModeRadialLinearPolynomialMode, finiteModeIdentityCoefficientCurve,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.pderiv_X,
    Pi.single_apply, MvPolynomial.eval_mul]
  ring

/-- The radial linear reconstruction has zero spatial Laplacian. -/
theorem finiteModeRadialLinear_spatialLaplacian_zero
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      0 := by
  rw [finiteModePolynomialReconstructedVelocity_spatialLaplacian
    finiteModeRadialLinearPolynomialMode finiteModeIdentityCoefficientCurve t x]
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialLaplacianComponents,
      finiteModePolynomialScalarLaplacian,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeRadialLinearPolynomialMode, finiteModeIdentityCoefficientCurve,
      finiteModePolynomialVectorFieldEval_apply, Fin.sum_univ_three,
      MvPolynomial.pderiv_X, Pi.single_apply]

/-- The radial linear example has the explicit closing pressure gradient
`-(1 + t^2) x`.  Viscosity drops out because the formal Laplacian of the
linear radial mode is zero. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_eq
    (ν t : ℝ) (j : Fin 3) :
    finiteModePolynomialClosingPressureGradientComponents
        ν finiteModeRadialLinearPolynomialMode
          finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents
              finiteModeRadialLinearPolynomialMode
              finiteModeIdentityCoefficientCurve s))
        t j =
      -(MvPolynomial.C (1 + t * t) * MvPolynomial.X j) := by
  fin_cases j <;>
    simp [finiteModePolynomialClosingPressureGradientComponents,
      finiteModePolynomialNonPressureDefectComponents,
      finiteModePolynomialReconstructedAccelerationComponents,
      finiteModePolynomialConvectionComponents,
      finiteModePolynomialLaplacianComponents,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeRadialLinearPolynomialMode,
      finiteModeProjectedNSRHS, finiteModeUnitForcingCoefficients,
      finiteModeIdentityCoefficientCurve, finiteModePolynomialScalarLaplacian,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply] <;>
    ring

/-- For the radial linear polynomial mode, the fully computed closing
pressure-gradient polynomial is curl-free.  This is a concrete positive check
of the polynomial closure condition including the convection and Laplacian
computations. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_curlFree
    (ν ε : ℝ) :
    ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      MvPolynomial.pderiv i
          (finiteModePolynomialClosingPressureGradientComponents
            ν finiteModeRadialLinearPolynomialMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents
                  finiteModeRadialLinearPolynomialMode
                  finiteModeIdentityCoefficientCurve s))
            t j) =
        MvPolynomial.pderiv j
          (finiteModePolynomialClosingPressureGradientComponents
            ν finiteModeRadialLinearPolynomialMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents
                  finiteModeRadialLinearPolynomialMode
                  finiteModeIdentityCoefficientCurve s))
            t i) := by
  intro t _ht i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteModePolynomialClosingPressureGradientComponents,
      finiteModePolynomialNonPressureDefectComponents,
      finiteModePolynomialReconstructedAccelerationComponents,
      finiteModePolynomialConvectionComponents,
      finiteModePolynomialLaplacianComponents,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeRadialLinearPolynomialMode,
      finiteModeProjectedNSRHS, finiteModeUnitForcingCoefficients,
      finiteModeIdentityCoefficientCurve, finiteModePolynomialScalarLaplacian,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply]

/-- The explicit polynomial primitive constructed for the radial linear mode has
pressure gradient `-(1 + t^2) x` on the local interval. -/
theorem finiteModeRadialLinearPolynomialPressureGradient_eq
    (ν ε : ℝ) {t : NSTime} (ht : t ∈ Ioo (-ε) ε) (x : NSSpace) :
    spatialPressureGradient
        (fun s y =>
          finiteModePolynomialPressureMode
            (finiteModePolynomialClosingPressureGradientComponents
              ν finiteModeRadialLinearPolynomialMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
                (fun r => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents
                    finiteModeRadialLinearPolynomialMode
                    finiteModeIdentityCoefficientCurve r))
              s) y)
        t x =
      -(1 + t * t) • x := by
  unfold spatialPressureGradient
  rw [finiteModePolynomialPressureMode_gradient
    (finiteModePolynomialClosingPressureGradientComponents
      ν finiteModeRadialLinearPolynomialMode
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
        (fun r => finiteModePolynomialLaplacianComponents
          (finiteModePolynomialReconstructedVelocityComponents
            finiteModeRadialLinearPolynomialMode
            finiteModeIdentityCoefficientCurve r))
      t)
    ((finiteModeRadialLinearPolynomialClosingPressureGradient_curlFree ν ε) t ht) x]
  ext j
  simp [finiteModePolynomialVectorFieldEval_apply,
    finiteModeRadialLinearPolynomialClosingPressureGradient_eq,
    MvPolynomial.eval_mul]
  ring

/-- Direct pointwise momentum identity for the radial linear reconstruction,
using the explicit pressure gradient formula. -/
theorem finiteModeRadialLinear_reconstructed_momentum_explicit
    (ν ε : ℝ) {t : NSTime} (ht : t ∈ Ioo (-ε) ε) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient
            (fun s y =>
              finiteModePolynomialPressureMode
                (finiteModePolynomialClosingPressureGradientComponents
                  ν finiteModeRadialLinearPolynomialMode
                    finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
                    (fun r => finiteModePolynomialLaplacianComponents
                      (finiteModePolynomialReconstructedVelocityComponents
                        finiteModeRadialLinearPolynomialMode
                        finiteModeIdentityCoefficientCurve r))
                  s) y)
            t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x := by
  rw [finiteModeRadialLinear_timeVelocityDerivative_eq t x,
    finiteModeRadialLinear_spatialConvection_eq t x,
    finiteModeRadialLinearPolynomialPressureGradient_eq ν ε ht x,
    finiteModeRadialLinear_spatialLaplacian_zero t x]
  ext j
  simp
  ring

/-- Diagonal-quadratic pressure coefficients for the radial-linear example:
each coordinate pressure mode receives coefficient `-(1+t^2)`. -/
def finiteModeRadialLinearDiagonalPressureCoefficients :
    NSTime → FiniteModeState (Fin 3) :=
  fun t _ => -(1 + t * t)

/-- The diagonal-quadratic pressure field closing the radial-linear example. -/
def finiteModeRadialLinearDiagonalPressure : NSPressureField :=
  finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
    finiteModeRadialLinearDiagonalPressureCoefficients

/-- The finite diagonal-quadratic pressure ansatz has the same explicit
pressure gradient `-(1+t^2)x` as the polynomial primitive construction. -/
theorem finiteModeRadialLinearDiagonalPressureGradient_eq
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient finiteModeRadialLinearDiagonalPressure t x =
      -(1 + t * t) • x := by
  rw [show finiteModeRadialLinearDiagonalPressure =
      finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
        (finiteModeDiagonalQuadraticPressureCoefficients
          finiteModeRadialLinearDiagonalPressureCoefficients) by
      rfl]
  rw [finiteModeDiagonalQuadraticPressure_spatialPressureGradient
    finiteModeRadialLinearDiagonalPressureCoefficients t x]
  ext j
  fin_cases j <;>
    simp [finiteModeRadialLinearDiagonalPressureCoefficients, Fin.sum_univ_three]

/-- Direct pointwise momentum identity for the radial-linear reconstruction
using the finite diagonal-quadratic pressure ansatz. -/
theorem finiteModeRadialLinear_diagonalPressure_reconstructed_momentum
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient finiteModeRadialLinearDiagonalPressure t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x := by
  rw [finiteModeRadialLinear_timeVelocityDerivative_eq t x,
    finiteModeRadialLinear_spatialConvection_eq t x,
    finiteModeRadialLinearDiagonalPressureGradient_eq t x,
    finiteModeRadialLinear_spatialLaplacian_zero t x]
  ext j
  simp
  ring

/-- The radial-linear diagonal-quadratic pressure ansatz has zero reconstructed
finite-mode momentum residual on every time set. -/
theorem finiteModeRadialLinear_diagonalPressure_reconstructedResidualZeroOn_univ
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeDiagonalQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearDiagonalPressureCoefficients := by
  intro t _ht x
  exact
    (finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
      ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeDiagonalQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearDiagonalPressureCoefficients t
      (finiteModeIdentityCoefficientCurve_hasDerivAt t) x).mpr
      (finiteModeRadialLinear_diagonalPressure_reconstructed_momentum ν t x)

/-- Existential packaging of the radial-linear solution with the finite
diagonal-quadratic pressure basis. -/
theorem finiteModeRadialLinear_reconstructed_velocityDiagonalPressure_momentum_exists
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeRadialLinearDiagonalPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  exact
    ⟨finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve,
      finiteModeRadialLinearDiagonalPressure, rfl, rfl,
      finiteModeRadialLinear_diagonalPressure_reconstructed_momentum ν⟩

/-- Concrete nonconstant positive instance of the polynomial finite-mode
pressure construction: the radial linear mode with the identity coefficient
curve admits the explicitly constructed polynomial pressure primitive closing
the local pointwise momentum equation. -/
theorem finiteModeRadialLinear_reconstructed_velocityPolynomialPressure_momentum_exists
    (ν ε : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = (fun t x =>
          finiteModePolynomialPressureMode
            (finiteModePolynomialClosingPressureGradientComponents
              ν finiteModeRadialLinearPolynomialMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents
                    finiteModeRadialLinearPolynomialMode
                    finiteModeIdentityCoefficientCurve s))
              t) x) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialModes_curlFree
      ν finiteModeRadialLinearPolynomialMode finiteModeUnitForcingCoefficients
      finiteModeIdentityCoefficientCurve ε
      (fun t _ht => finiteModeIdentityCoefficientCurve_hasDerivAt t)
      (finiteModeRadialLinearPolynomialClosingPressureGradient_curlFree ν ε)

/-- Affine Helmholtz closure theorem for the finite-mode reconstruction: if the
non-pressure defect is an affine vector field with symmetric linear part, the
affine-quadratic pressure basis constructs coefficients closing momentum. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_affineHelmholtz
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (c : NSTime → NSSpace)
    (A : NSTime → Fin 3 → Fin 3 → ℝ)
    (hA : ∀ t ∈ Ioo (-ε) ε, ∀ i j, A t i j = A t j i)
    (hdefect : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModeAffineGradientField (c t) (A t)) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode finiteModeAffineQuadraticPressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureHelmholtzRange
      ν mode finiteModeAffineQuadraticPressureMode C a ε ha
      (fun k x => finiteModeAffineQuadraticPressureMode_differentiableAt k x) ?_
  intro t ht
  rw [hdefect t ht]
  exact finiteModeAffineQuadraticPressureGradient_mem_range (c t) (A t) (hA t ht)

/-- Polynomial-mode affine finite-pressure closure: if the fully computed
closing pressure-gradient polynomial is an affine vector field with symmetric
linear part, the affine-quadratic pressure basis constructs finite pressure
coefficients closing the reconstructed pointwise momentum equation. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (c : NSTime → NSSpace)
    (A : NSTime → Fin 3 → Fin 3 → ℝ)
    (hA : ∀ t ∈ Ioo (-ε) ε, ∀ i j, A t i j = A t j i)
    (hclosing : ∀ t ∈ Ioo (-ε) ε,
      finiteModePolynomialVectorFieldEval
          (finiteModePolynomialClosingPressureGradientComponents
            ν modePoly C a
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
            t) =
        finiteModeAffineGradientField (c t) (A t)) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y)
              finiteModeAffineQuadraticPressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_affineHelmholtz
      ν (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y)
      C a ε ha c A hA ?_
  intro t ht
  funext x
  calc
    (-finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t) x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν modePoly C a
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
          t) x := by
        ext j
        have hdefj := congrArg (fun v : NSSpace => v j)
          (finiteModePolynomialNonPressureDefect_eq_eval ν modePoly C a t x)
        simp [finiteModePolynomialClosingPressureGradientComponents,
          finiteModePolynomialVectorFieldEval_apply, hdefj]
    _ = finiteModeAffineGradientField (c t) (A t) x := by
        exact congrFun (hclosing t ht) x

/-- Zero affine offset for the affine-quadratic presentation of the
radial-linear pressure gradient. -/
def finiteModeRadialLinearAffinePressureConstant : NSTime → NSSpace :=
  fun _ => 0

/-- Diagonal matrix for the affine-gradient presentation of
`-(1+t^2)x`. -/
def finiteModeRadialLinearAffinePressureMatrix
    (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = j then -(1 + t * t) else 0

/-- The radial-linear affine pressure matrix is symmetric. -/
theorem finiteModeRadialLinearAffinePressureMatrix_symm
    (t : NSTime) :
    ∀ i j, finiteModeRadialLinearAffinePressureMatrix t i j =
      finiteModeRadialLinearAffinePressureMatrix t j i := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [finiteModeRadialLinearAffinePressureMatrix]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [finiteModeRadialLinearAffinePressureMatrix, hij, hji]

/-- The affine-gradient presentation of the radial-linear pressure gradient is
the vector field `-(1+t^2)x`. -/
theorem finiteModeRadialLinearAffineGradientField_eq
    (t : NSTime) (x : NSSpace) :
    finiteModeAffineGradientField
        (finiteModeRadialLinearAffinePressureConstant t)
        (finiteModeRadialLinearAffinePressureMatrix t) x =
      -(1 + t * t) • x := by
  ext j
  fin_cases j <;>
    simp [finiteModeAffineGradientField,
      finiteModeRadialLinearAffinePressureConstant,
      finiteModeRadialLinearAffinePressureMatrix,
      Fin.sum_univ_three]

/-- The computed radial-linear polynomial closing pressure gradient evaluates
to the explicit vector field `-(1+t^2)x`. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_eval_eq
    (ν t : ℝ) (x : NSSpace) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν finiteModeRadialLinearPolynomialMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                finiteModeRadialLinearPolynomialMode
                finiteModeIdentityCoefficientCurve s))
          t) x =
      -(1 + t * t) • x := by
  ext j
  simp [finiteModePolynomialVectorFieldEval_apply,
    finiteModeRadialLinearPolynomialClosingPressureGradient_eq,
    MvPolynomial.eval_mul]
  ring

/-- The computed radial-linear polynomial closing pressure gradient is an
affine symmetric gradient field, so it lies in the finite affine-quadratic
pressure basis. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_affine_eq
    (ν t : ℝ) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν finiteModeRadialLinearPolynomialMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                finiteModeRadialLinearPolynomialMode
                finiteModeIdentityCoefficientCurve s))
          t) =
      finiteModeAffineGradientField
        (finiteModeRadialLinearAffinePressureConstant t)
        (finiteModeRadialLinearAffinePressureMatrix t) := by
  funext x
  rw [finiteModeRadialLinearPolynomialClosingPressureGradient_eval_eq ν t x,
    finiteModeRadialLinearAffineGradientField_eq t x]

/-- Explicit affine-quadratic pressure coefficients for the radial-linear
example.  Only the diagonal quadratic slots are nonzero. -/
def finiteModeRadialLinearAffineQuadraticPressureCoefficients :
    NSTime → FiniteModeState FiniteModeAffineQuadraticPressureIndex :=
  fun t =>
    finiteModeAffineQuadraticPressureCoefficientsAt
      (finiteModeRadialLinearAffinePressureConstant t)
      (finiteModeRadialLinearAffinePressureMatrix t)

/-- The explicit affine-quadratic pressure field closing the radial-linear
example. -/
def finiteModeRadialLinearAffineQuadraticPressure : NSPressureField :=
  finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode
    finiteModeRadialLinearAffineQuadraticPressureCoefficients

/-- The explicit affine-quadratic pressure has spatial gradient
`-(1+t^2)x`. -/
theorem finiteModeRadialLinearAffineQuadraticPressureGradient_eq
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient finiteModeRadialLinearAffineQuadraticPressure t x =
      -(1 + t * t) • x := by
  unfold finiteModeRadialLinearAffineQuadraticPressure
  rw [finiteModeReconstructedPressure_spatialPressureGradient
    finiteModeAffineQuadraticPressureMode
    finiteModeRadialLinearAffineQuadraticPressureCoefficients t x
    (fun k => finiteModeAffineQuadraticPressureMode_differentiableAt k x)]
  change
    finiteModePressureGradientSynthesis finiteModeAffineQuadraticPressureMode
        (finiteModeAffineQuadraticPressureCoefficientsAt
          (finiteModeRadialLinearAffinePressureConstant t)
          (finiteModeRadialLinearAffinePressureMatrix t)) x =
      -(1 + t * t) • x
  rw [finiteModeAffineQuadraticPressureGradientSynthesis
    (finiteModeRadialLinearAffinePressureConstant t)
    (finiteModeRadialLinearAffinePressureMatrix t)
    (finiteModeRadialLinearAffinePressureMatrix_symm t) x,
    finiteModeRadialLinearAffineGradientField_eq t x]

/-- Direct pointwise momentum identity for the radial-linear reconstruction
using the explicit affine-quadratic pressure coefficients. -/
theorem finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient finiteModeRadialLinearAffineQuadraticPressure t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x := by
  rw [finiteModeRadialLinear_timeVelocityDerivative_eq t x,
    finiteModeRadialLinear_spatialConvection_eq t x,
    finiteModeRadialLinearAffineQuadraticPressureGradient_eq t x,
    finiteModeRadialLinear_spatialLaplacian_zero t x]
  ext j
  simp
  ring

/-- The explicit affine-quadratic pressure coefficients give zero
reconstructed finite-mode momentum residual for the radial-linear example. -/
theorem finiteModeRadialLinear_affineQuadraticPressure_reconstructedResidualZeroOn_univ
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeAffineQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearAffineQuadraticPressureCoefficients := by
  intro t _ht x
  exact
    (finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
      ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeAffineQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearAffineQuadraticPressureCoefficients t
      (finiteModeIdentityCoefficientCurve_hasDerivAt t) x).mpr
      (by
        simpa [finiteModeRadialLinearAffineQuadraticPressure] using
          finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum ν t x)

/-- Existential packaging of the radial-linear solution with the explicit
affine-quadratic pressure field, without using synthesized coefficients. -/
theorem finiteModeRadialLinear_reconstructed_velocityExplicitAffineQuadraticPressure_momentum_exists
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeRadialLinearAffineQuadraticPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  exact
    ⟨finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve,
      finiteModeRadialLinearAffineQuadraticPressure, rfl, rfl,
      finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum ν⟩

/-- The radial-linear polynomial mode also closes through the finite
affine-quadratic pressure basis via the polynomial-to-affine bridge theorem. -/
theorem finiteModeRadialLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists
    (ν ε : ℝ) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeRadialLinearPolynomialMode i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
      ν finiteModeRadialLinearPolynomialMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve ε
      (fun t _ht => finiteModeIdentityCoefficientCurve_hasDerivAt t)
      finiteModeRadialLinearAffinePressureConstant
      finiteModeRadialLinearAffinePressureMatrix
      (fun t _ht => finiteModeRadialLinearAffinePressureMatrix_symm t)
      (fun t _ht => finiteModeRadialLinearPolynomialClosingPressureGradient_affine_eq ν t)

end NavierStokes
end FluidDynamics
end Mettapedia
