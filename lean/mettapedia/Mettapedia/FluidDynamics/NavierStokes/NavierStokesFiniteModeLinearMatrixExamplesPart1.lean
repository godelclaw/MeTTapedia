import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeLinearIncompressibleExamples

/-!
# General trace-free linear-matrix finite-mode examples, pressure closure, smoothness, and energy obstruction.
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


/-- A fixed linear matrix velocity mode `x ↦ A x`, represented polynomially. -/

def finiteModeLinearMatrixPolynomialMode
    (A : Fin 3 → Fin 3 → ℝ) (_ : PUnit) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => ∑ k : Fin 3, MvPolynomial.C (A j k) * MvPolynomial.X k

/-- Kinetic-energy density associated to a linear spatial velocity profile.
This isolates the whole-space energy obstruction for polynomial linear modes:
nonzero linear growth on `ℝ^3` is not spatially integrable. -/
def finiteModeLinearMapKineticEnergyDensity
    (L : NSSpace →L[ℝ] NSSpace) : NSSpace → ℝ :=
  fun x => ‖L x‖ ^ (2 : ℕ)

/-- Linear-map kinetic-energy densities are continuous. -/
theorem finiteModeLinearMapKineticEnergyDensity_continuous
    (L : NSSpace →L[ℝ] NSSpace) :
    Continuous (finiteModeLinearMapKineticEnergyDensity L) := by
  simpa [finiteModeLinearMapKineticEnergyDensity] using (L.continuous.norm.pow 2)

/-- A nonzero linear spatial velocity profile has nonintegrable kinetic-energy
density on `ℝ^3`.  The proof is the Haar-scaling obstruction: the density scales
like `R^2`, while three-dimensional volume scales like `R^3`. -/
theorem not_integrable_finiteModeLinearMapKineticEnergyDensity
    {L : NSSpace →L[ℝ] NSSpace}
    (hL : L ≠ 0) :
    ¬ MeasureTheory.Integrable (finiteModeLinearMapKineticEnergyDensity L) := by
  intro hInt
  have hpoint : ∃ x : NSSpace, L x ≠ 0 := by
    by_contra hnone
    apply hL
    ext x i
    by_contra hx
    have hLx : L x ≠ 0 := by
      intro hzero
      exact hx (congrArg (fun v : NSSpace => v i) hzero)
    exact hnone ⟨x, hLx⟩
  rcases hpoint with ⟨x₀, hx₀⟩
  have hnonneg : ∀ x, 0 ≤ finiteModeLinearMapKineticEnergyDensity L x := by
    intro x
    simpa [finiteModeLinearMapKineticEnergyDensity, pow_two] using
      (mul_self_nonneg ‖L x‖)
  have hx₀pos : finiteModeLinearMapKineticEnergyDensity L x₀ ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx₀)
  have hpos : 0 < ∫ x, finiteModeLinearMapKineticEnergyDensity L x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x₀)
      (finiteModeLinearMapKineticEnergyDensity_continuous L)
      hInt hnonneg hx₀pos
  let I : ℝ := ∫ x, finiteModeLinearMapKineticEnergyDensity L x
  have hcomp :
      ∫ x, finiteModeLinearMapKineticEnergyDensity L ((2 : ℝ) • x) = (4 : ℝ) * I := by
    calc
      ∫ x, finiteModeLinearMapKineticEnergyDensity L ((2 : ℝ) • x)
          = ∫ x, (4 : ℝ) * finiteModeLinearMapKineticEnergyDensity L x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [finiteModeLinearMapKineticEnergyDensity, pow_two, norm_smul]
              ring
      _ = (4 : ℝ) * I := by
            simp [I, MeasureTheory.integral_const_mul]
  have hchange :
      ∫ x, finiteModeLinearMapKineticEnergyDensity L ((2 : ℝ) • x) =
        ((2 : ℝ) ^ Module.finrank ℝ NSSpace)⁻¹ * I := by
    simpa [smul_eq_mul, I] using
      (MeasureTheory.Measure.integral_comp_smul_of_nonneg
        (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
        (f := finiteModeLinearMapKineticEnergyDensity L)
        (R := (2 : ℝ)) (hR := by positivity))
  have hEq :
      (4 : ℝ) * I = ((2 : ℝ) ^ Module.finrank ℝ NSSpace)⁻¹ * I := by
    rw [← hcomp]
    exact hchange
  have hzero : I = 0 := by
    norm_num at hEq
    linarith
  have hIpos : 0 < I := by
    simpa [I] using hpos
  linarith

/-- Continuous linear map for a concrete matrix acting on `NSSpace`. -/
def finiteModeLinearMatrixCLM
    (A : Fin 3 → Fin 3 → ℝ) : NSSpace →L[ℝ] NSSpace :=
  ∑ i : Fin 3,
    (∑ j : Fin 3, A i j • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)).smulRight
      (EuclideanSpace.single i (1 : ℝ))

@[simp]
theorem finiteModeLinearMatrixCLM_apply
    (A : Fin 3 → Fin 3 → ℝ) (x : NSSpace) (i : Fin 3) :
    finiteModeLinearMatrixCLM A x i = ∑ j : Fin 3, A i j * x j := by
  simp [finiteModeLinearMatrixCLM, Pi.single_apply]

/-- A matrix with a nonzero entry gives a nonzero linear map on `NSSpace`. -/
theorem finiteModeLinearMatrixCLM_ne_zero_of_entry_ne
    {A : Fin 3 → Fin 3 → ℝ} {i j : Fin 3}
    (hA : A i j ≠ 0) :
    finiteModeLinearMatrixCLM A ≠ 0 := by
  intro hzero
  have hcomp :=
    congrArg
      (fun L : NSSpace →L[ℝ] NSSpace => L (EuclideanSpace.single j (1 : ℝ)) i)
      hzero
  simp [finiteModeLinearMatrixCLM, Pi.single_apply] at hcomp
  exact hA hcomp

/-- Matrix square coefficients for the linear matrix mode. -/
def finiteModeMatrixSquare (A : Fin 3 → Fin 3 → ℝ) :
    Fin 3 → Fin 3 → ℝ :=
  fun i j => ∑ k : Fin 3, A i k * A k j

/-- The affine pressure matrix closing `u(t,x)=t A x`. -/
def finiteModeLinearMatrixAffinePressureMatrix
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j => -(A i j + t * t * finiteModeMatrixSquare A i j)

/-- The square of a symmetric matrix is symmetric. -/
theorem finiteModeMatrixSquare_symm
    (A : Fin 3 → Fin 3 → ℝ) (hA : ∀ i j, A i j = A j i) :
    ∀ i j, finiteModeMatrixSquare A i j = finiteModeMatrixSquare A j i := by
  intro i j
  unfold finiteModeMatrixSquare
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hA i k, hA k j]
  ring

/-- The linear-matrix affine pressure matrix is symmetric when `A` is
symmetric. -/
theorem finiteModeLinearMatrixAffinePressureMatrix_symm
    (A : Fin 3 → Fin 3 → ℝ) (hA : ∀ i j, A i j = A j i) (t : NSTime) :
    ∀ i j, finiteModeLinearMatrixAffinePressureMatrix A t i j =
      finiteModeLinearMatrixAffinePressureMatrix A t j i := by
  intro i j
  simp [finiteModeLinearMatrixAffinePressureMatrix, hA i j,
    finiteModeMatrixSquare_symm A hA i j]

/-- Component formula for the matrix-linear reconstruction:
`u_j(t,x)=t Σ_k A_{jk} x_k`. -/
theorem finiteModeLinearMatrix_reconstructedVelocity_apply
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve t x j =
      t * ∑ k : Fin 3, A j k * x k := by
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeIdentityCoefficientCurve, finiteModeLinearMatrixPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul,
      Fin.sum_univ_three]

/-- The computed closing pressure gradient for `u(t,x)=t A x` is the affine
field `-(A + t^2 A^2)x`. -/
theorem finiteModeLinearMatrixPolynomialClosingPressureGradient_affine_eq
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν (finiteModeLinearMatrixPolynomialMode A)
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                (finiteModeLinearMatrixPolynomialMode A)
                finiteModeIdentityCoefficientCurve s))
          t) =
      finiteModeAffineGradientField 0
        (finiteModeLinearMatrixAffinePressureMatrix A t) := by
  funext x
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialClosingPressureGradientComponents,
      finiteModePolynomialNonPressureDefectComponents,
      finiteModePolynomialReconstructedAccelerationComponents,
      finiteModePolynomialConvectionComponents,
      finiteModePolynomialLaplacianComponents,
      finiteModePolynomialScalarLaplacian,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeLinearMatrixPolynomialMode,
      finiteModeProjectedNSRHS,
      finiteModeUnitForcingCoefficients,
      finiteModeIdentityCoefficientCurve,
      finiteModeAffineGradientField,
      finiteModeLinearMatrixAffinePressureMatrix,
      finiteModeMatrixSquare,
      finiteModePolynomialVectorFieldEval_apply,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.eval_mul] <;>
    ring_nf

/-- The divergence of the matrix-linear polynomial mode is the trace of `A`. -/
theorem finiteModeLinearMatrixPolynomialMode_spatialDivergence
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (fun _ : NSTime => fun y : NSSpace =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A PUnit.unit) y) t x =
      ∑ i : Fin 3, A i i := by
  unfold spatialDivergence spatialFDeriv
  change
    (∑ j : Fin 3,
      (fderiv ℝ
          (finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A PUnit.unit)) x
        (EuclideanSpace.single j (1 : ℝ))) j) =
      ∑ i : Fin 3, A i i
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModeLinearMatrixPolynomialMode A PUnit.unit) x).fderiv]
  simp [finiteModeLinearMatrixPolynomialMode,
    finiteModePolynomialVectorFieldFDeriv_apply, Fin.sum_univ_three,
    MvPolynomial.pderiv_X, Pi.single_apply]

/-- The divergence of `u(t,x)=t A x` is `t * trace A`. -/
theorem finiteModeLinearMatrix_spatialDivergence_eq
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeLinearMatrixPolynomialMode A i) y)
          finiteModeIdentityCoefficientCurve) t x =
      t * ∑ i : Fin 3, A i i := by
  rw [finiteModeReconstructedVelocity_spatialDivergence
    (fun i y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeLinearMatrixPolynomialMode A i) y)
    finiteModeIdentityCoefficientCurve t x]
  · rw [Fintype.sum_eq_single PUnit.unit]
    rw [finiteModeLinearMatrixPolynomialMode_spatialDivergence]
    simp [finiteModeIdentityCoefficientCurve]
    intro i hi
    cases i
    exact (hi rfl).elim
  · intro i
    cases i
    exact (finiteModePolynomialVectorFieldEval_hasFDerivAt
      (finiteModeLinearMatrixPolynomialMode A PUnit.unit) x).differentiableAt

/-- Trace-free matrix-linear velocities are divergence-free. -/
theorem finiteModeLinearMatrix_spatialDivergence_zero_of_trace
    (A : Fin 3 → Fin 3 → ℝ) (htrace : ∑ i : Fin 3, A i i = 0) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeLinearMatrixPolynomialMode A i) y)
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  intro t x
  rw [finiteModeLinearMatrix_spatialDivergence_eq A t x, htrace, mul_zero]

/-- Matrix-level closure under the exact affine-pressure condition: if the
computed affine closing matrix is symmetric on the local interval, and the
velocity matrix is trace-free, then `u(t,x)=t A x` admits finite
affine-quadratic pressure closure and is incompressible. -/
theorem finiteModeLinearMatrix_traceFreeAffineSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    (ν ε : ℝ) (A : Fin 3 → Fin 3 → ℝ)
    (hclosure : ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      finiteModeLinearMatrixAffinePressureMatrix A t i j =
        finiteModeLinearMatrixAffinePressureMatrix A t j i)
    (htrace : ∑ i : Fin 3, A i i = 0) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeLinearMatrixPolynomialMode A i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 := by
  rcases
    finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
      ν (finiteModeLinearMatrixPolynomialMode A)
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve ε
      (fun t _ht => finiteModeIdentityCoefficientCurve_hasDerivAt t)
      (fun _ => 0)
      (finiteModeLinearMatrixAffinePressureMatrix A)
      hclosure
      (fun t _ht =>
        finiteModeLinearMatrixPolynomialClosingPressureGradient_affine_eq ν A t) with
    ⟨b, u, p, hu, hp, hres, hmom⟩
  refine ⟨b, u, p, hu, hp, hres, hmom, ?_⟩
  intro t x
  rw [hu]
  exact finiteModeLinearMatrix_spatialDivergence_zero_of_trace A htrace t x

/-- Matrix-level positive construction: every symmetric trace-free matrix
linear field `u(t,x)=t A x` admits finite affine-quadratic pressure closure and
is incompressible. -/
theorem finiteModeLinearMatrix_traceFreeSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    (ν ε : ℝ) (A : Fin 3 → Fin 3 → ℝ)
    (hA : ∀ i j, A i j = A j i) (htrace : ∑ i : Fin 3, A i i = 0) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeLinearMatrixPolynomialMode A i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 := by
  exact
    finiteModeLinearMatrix_traceFreeAffineSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
      ν ε A (fun t _ht => finiteModeLinearMatrixAffinePressureMatrix_symm A hA t)
      htrace

/-- The time-dependent matrix-linear velocity `u(t,x)=g(t) A x`, represented
using the same one-mode polynomial reconstruction surface. -/
end NavierStokes
end FluidDynamics
end Mettapedia
