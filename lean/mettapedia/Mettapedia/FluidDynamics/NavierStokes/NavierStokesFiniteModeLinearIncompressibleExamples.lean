import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeRadialLinearExamples

/-!
# Diagonal and symmetric linear incompressible finite-mode examples with affine-quadratic pressure closure.
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

/-- Three diagonal linear polynomial modes: mode `i` is the vector field
`x_i e_i`.  Unlike the one-mode radial-linear example, the three coordinate
directions now carry independent amplitudes. -/
def finiteModeDiagonalLinearPolynomialMode (i : Fin 3) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  Pi.single i (MvPolynomial.X i)

/-- Constant projected forcing for the diagonal-linear three-mode family. -/
def finiteModeDiagonalLinearForcingCoefficients
    (lam : Fin 3 → ℝ) : FiniteModeProjectedNSCoefficients (Fin 3) where
  forcing := lam
  linear := fun _ _ => 0
  quadratic := fun _ _ _ => 0

/-- The diagonal-linear forced projected system has constant RHS `lam`. -/
@[simp]
theorem finiteModeDiagonalLinearForcingCoefficients_rhs
    (lam : Fin 3 → ℝ) (a : FiniteModeState (Fin 3)) (i : Fin 3) :
    finiteModeProjectedNSRHS
        (finiteModeDiagonalLinearForcingCoefficients lam) a i =
      lam i := by
  simp [finiteModeProjectedNSRHS, finiteModeDiagonalLinearForcingCoefficients]

/-- Independent linear-in-time amplitudes for the diagonal-linear family. -/
def finiteModeDiagonalLinearCoefficientCurve
    (lam : Fin 3 → ℝ) : ℝ → FiniteModeState (Fin 3) :=
  fun t i => lam i * t

/-- The diagonal-linear coefficient curve solves the forced diagonal projected
ODE with no linear or quadratic coefficient interactions. -/
theorem finiteModeDiagonalLinearCoefficientCurve_hasDerivAt
    (lam : Fin 3 → ℝ) (t : NSTime) :
    HasDerivAt (finiteModeDiagonalLinearCoefficientCurve lam)
      (finiteModeProjectedNSRHS (finiteModeDiagonalLinearForcingCoefficients lam)
        (finiteModeDiagonalLinearCoefficientCurve lam t)) t := by
  rw [hasDerivAt_pi]
  intro i
  simpa [finiteModeDiagonalLinearCoefficientCurve, finiteModeProjectedNSRHS,
    finiteModeDiagonalLinearForcingCoefficients] using
    (hasDerivAt_id t).const_mul (lam i)

/-- Component formula for the anisotropic diagonal-linear reconstructed
velocity: `u_i(t,x)=lam_i t x_i`. -/
theorem finiteModeDiagonalLinear_reconstructedVelocity_apply
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) t x j =
      lam j * t * x j := by
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeDiagonalLinearCoefficientCurve,
      finiteModeDiagonalLinearPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply,
      Fin.sum_univ_three]

/-- Diagonal matrix for the affine-gradient presentation of the pressure
gradient closing the anisotropic diagonal-linear velocity family. -/
def finiteModeDiagonalLinearAffinePressureMatrix
    (lam : Fin 3 → ℝ) (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = j then -(lam i + (lam i * t) * (lam i * t)) else 0

/-- The diagonal-linear affine pressure matrix is symmetric. -/
theorem finiteModeDiagonalLinearAffinePressureMatrix_symm
    (lam : Fin 3 → ℝ) (t : NSTime) :
    ∀ i j, finiteModeDiagonalLinearAffinePressureMatrix lam t i j =
      finiteModeDiagonalLinearAffinePressureMatrix lam t j i := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [finiteModeDiagonalLinearAffinePressureMatrix]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [finiteModeDiagonalLinearAffinePressureMatrix, hij, hji]

/-- The affine-gradient presentation of the diagonal-linear closing pressure
gradient. -/
theorem finiteModeDiagonalLinearAffineGradientField_eq
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    finiteModeAffineGradientField 0
        (finiteModeDiagonalLinearAffinePressureMatrix lam t) x =
      fun j => -(lam j + (lam j * t) * (lam j * t)) * x j := by
  ext j
  fin_cases j <;>
    simp [finiteModeAffineGradientField,
      finiteModeDiagonalLinearAffinePressureMatrix,
      Fin.sum_univ_three]

/-- The fully computed polynomial closing pressure gradient for the
diagonal-linear three-mode family is affine with symmetric diagonal linear
part.  Viscosity drops out because the modes are spatially linear. -/
theorem finiteModeDiagonalLinearPolynomialClosingPressureGradient_affine_eq
    (ν : ℝ) (lam : Fin 3 → ℝ) (t : NSTime) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν finiteModeDiagonalLinearPolynomialMode
            (finiteModeDiagonalLinearForcingCoefficients lam)
            (finiteModeDiagonalLinearCoefficientCurve lam)
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                finiteModeDiagonalLinearPolynomialMode
                (finiteModeDiagonalLinearCoefficientCurve lam) s))
          t) =
      finiteModeAffineGradientField 0
        (finiteModeDiagonalLinearAffinePressureMatrix lam t) := by
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
      finiteModeDiagonalLinearPolynomialMode,
      finiteModeProjectedNSRHS,
      finiteModeDiagonalLinearForcingCoefficients,
      finiteModeDiagonalLinearCoefficientCurve,
      finiteModeAffineGradientField,
      finiteModeDiagonalLinearAffinePressureMatrix,
      finiteModePolynomialVectorFieldEval_apply,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.eval_mul] <;>
    ring_nf

/-- Multi-mode positive instance: every anisotropic diagonal-linear velocity
family `u_i(t,x)=lam_i t x_i` admits affine-quadratic finite pressure
coefficients closing the reconstructed local pointwise momentum equation. -/
theorem finiteModeDiagonalLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists
    (ν ε : ℝ) (lam : Fin 3 → ℝ) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeDiagonalLinearPolynomialMode i) y)
              finiteModeAffineQuadraticPressureMode
              (finiteModeDiagonalLinearForcingCoefficients lam)
              (finiteModeDiagonalLinearCoefficientCurve lam) b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
      ν finiteModeDiagonalLinearPolynomialMode
      (finiteModeDiagonalLinearForcingCoefficients lam)
      (finiteModeDiagonalLinearCoefficientCurve lam) ε
      (fun t _ht => finiteModeDiagonalLinearCoefficientCurve_hasDerivAt lam t)
      (fun _ => 0)
      (finiteModeDiagonalLinearAffinePressureMatrix lam)
      (fun t _ht => finiteModeDiagonalLinearAffinePressureMatrix_symm lam t)
      (fun t _ht => finiteModeDiagonalLinearPolynomialClosingPressureGradient_affine_eq ν lam t)

/-- Each diagonal-linear polynomial mode is differentiable at every spatial
point. -/
theorem finiteModeDiagonalLinearPolynomialMode_differentiableAt
    (i : Fin 3) (x : NSSpace) :
    DifferentiableAt ℝ
      (fun y : NSSpace =>
        finiteModePolynomialVectorFieldEval
          (finiteModeDiagonalLinearPolynomialMode i) y) x :=
  (finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModeDiagonalLinearPolynomialMode i) x).differentiableAt

/-- Each diagonal-linear mode `x_i e_i` has spatial divergence `1`. -/
theorem finiteModeDiagonalLinearPolynomialMode_spatialDivergence
    (i : Fin 3) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (fun _ : NSTime => fun y : NSSpace =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y) t x = 1 := by
  unfold spatialDivergence spatialFDeriv
  change
    (∑ j : Fin 3,
      (fderiv ℝ
          (finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i)) x
        (EuclideanSpace.single j (1 : ℝ))) j) = 1
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModeDiagonalLinearPolynomialMode i) x).fderiv]
  fin_cases i <;>
    simp [finiteModeDiagonalLinearPolynomialMode,
      finiteModePolynomialVectorFieldFDeriv_apply, Fin.sum_univ_three,
      MvPolynomial.pderiv_X, Pi.single_apply]

/-- If the non-pressure finite-mode residual is closed by a spatially constant
time-dependent vector `c(t)`, the coordinate pressure modes construct a concrete
pressure field whose gradient is `c(t)` and hence close the local momentum
equation. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityCoordinatePressure_momentum_of_constantGradient_balance
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (c : NSTime → NSSpace)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hbalance : ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            c t =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure finiteModeCoordinatePressureMode
          (finiteModeCoordinatePressureCoefficients c) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureModeGradient_balance
      ν mode finiteModeCoordinatePressureMode C a
      (finiteModeCoordinatePressureCoefficients c) ε ha
      (fun j x => finiteModeCoordinatePressureMode_differentiableAt j x) ?_
  intro t ht x
  have hgrad :
      (∑ j : Fin 3,
        finiteModeCoordinatePressureCoefficients c t j •
          gradient (finiteModeCoordinatePressureMode j) x) = c t := by
    calc
      (∑ j : Fin 3,
        finiteModeCoordinatePressureCoefficients c t j •
          gradient (finiteModeCoordinatePressureMode j) x) =
        ∑ j : Fin 3, c t j • EuclideanSpace.single j (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [finiteModeCoordinatePressureMode_gradient]
          rfl
      _ = c t := finiteModeCoordinatePressureMode_gradient_sum (c t)
  rw [hgrad]
  exact hbalance t ht x

/-- If the non-pressure finite-mode residual is closed by a diagonal
linear-in-space gradient field, the diagonal quadratic pressure modes construct
a nonconstant pressure field and close the local momentum equation. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityDiagonalQuadraticPressure_momentum_of_diagonalLinearGradient_balance
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (d : NSTime → FiniteModeState (Fin 3))
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hbalance : ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            (∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ))) =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
          (finiteModeDiagonalQuadraticPressureCoefficients d) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureModeGradient_balance
      ν mode finiteModeDiagonalQuadraticPressureMode C a
      (finiteModeDiagonalQuadraticPressureCoefficients d) ε ha
      (fun j x => finiteModeDiagonalQuadraticPressureMode_differentiableAt j x) ?_
  intro t ht x
  have hgrad :
      (∑ j : Fin 3,
        finiteModeDiagonalQuadraticPressureCoefficients d t j •
          gradient (finiteModeDiagonalQuadraticPressureMode j) x) =
        ∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [finiteModeDiagonalQuadraticPressureMode_gradient]
    rfl
  rw [hgrad]
  exact hbalance t ht x

/-- Spatial divergence of a reconstructed finite-mode velocity is the finite
sum of the modal divergences weighted by the current coefficients. -/
theorem finiteModeReconstructedVelocity_spatialDivergence
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace)
    (hmode : ∀ i, DifferentiableAt ℝ (mode i) x) :
    spatialDivergence (finiteModeReconstructedVelocity mode a) t x =
      ∑ i : ι, a t i *
        spatialDivergence (fun _ : NSTime => mode i) t x := by
  unfold spatialDivergence spatialFDeriv
  have hdiff :
      ∀ i ∈ (Finset.univ : Finset ι),
        DifferentiableAt ℝ (fun y : NSSpace => a t i • mode i y) x := by
    intro i _hi
    exact (hmode i).const_smul (a t i)
  have hfderiv :
      fderiv ℝ (fun y : NSSpace => finiteModeReconstructedVelocity mode a t y) x =
        ∑ i : ι, fderiv ℝ (fun y : NSSpace => a t i • mode i y) x := by
    simpa [finiteModeReconstructedVelocity, finiteModeReconstructionCLM] using
      (fderiv_fun_sum hdiff)
  rw [hfderiv]
  calc
    ∑ j : Fin 3,
        ((∑ i : ι, fderiv ℝ (fun y : NSSpace => a t i • mode i y) x)
            (EuclideanSpace.single j (1 : ℝ))) j =
      ∑ j : Fin 3,
        ∑ i : ι,
          (fderiv ℝ (fun y : NSSpace => a t i • mode i y) x
            (EuclideanSpace.single j (1 : ℝ))) j := by
        simp
    _ =
      ∑ i : ι,
        ∑ j : Fin 3,
          (fderiv ℝ (fun y : NSSpace => a t i • mode i y) x
            (EuclideanSpace.single j (1 : ℝ))) j := by
        rw [Finset.sum_comm]
    _ =
      ∑ i : ι, a t i *
        ∑ j : Fin 3,
          (fderiv ℝ (fun y : NSSpace => mode i y) x
            (EuclideanSpace.single j (1 : ℝ))) j := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [fderiv_fun_const_smul (hmode i) (a t i)]
        simp [Finset.mul_sum]
    _ =
      ∑ i : ι, a t i *
        spatialDivergence (fun _ : NSTime => mode i) t x := by
        rfl

/-- If every selected mode is divergence-free, the reconstructed velocity is
divergence-free at every point. -/
theorem finiteModeReconstructedVelocity_spatialDivergence_zero
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (a : ℝ → FiniteModeState ι)
    (hmodeDiff : ∀ i x, DifferentiableAt ℝ (mode i) x)
    (hmodeDiv : ∀ i t x, spatialDivergence (fun _ : NSTime => mode i) t x = 0) :
    ∀ t x, spatialDivergence (finiteModeReconstructedVelocity mode a) t x = 0 := by
  intro t x
  rw [finiteModeReconstructedVelocity_spatialDivergence mode a t x
    (fun i => hmodeDiff i x)]
  simp [hmodeDiv]

/-- The divergence of the diagonal-linear reconstruction is the trace of its
coefficient vector, multiplied by time. -/
theorem finiteModeDiagonalLinear_spatialDivergence_eq
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeDiagonalLinearPolynomialMode i) y)
          (finiteModeDiagonalLinearCoefficientCurve lam)) t x =
      t * ∑ i : Fin 3, lam i := by
  rw [finiteModeReconstructedVelocity_spatialDivergence
    (fun i y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeDiagonalLinearPolynomialMode i) y)
    (finiteModeDiagonalLinearCoefficientCurve lam) t x
    (fun i => finiteModeDiagonalLinearPolynomialMode_differentiableAt i x)]
  calc
    (∑ i : Fin 3,
        finiteModeDiagonalLinearCoefficientCurve lam t i *
          spatialDivergence
            (fun _ : NSTime => fun y : NSSpace =>
              finiteModePolynomialVectorFieldEval
                (finiteModeDiagonalLinearPolynomialMode i) y) t x) =
        ∑ i : Fin 3, lam i * t := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [finiteModeDiagonalLinearCoefficientCurve,
        finiteModeDiagonalLinearPolynomialMode_spatialDivergence]
    _ = (∑ i : Fin 3, lam i) * t := by
      rw [Finset.sum_mul]
    _ = t * ∑ i : Fin 3, lam i := by
      ring

/-- Trace-free diagonal-linear coefficients give a divergence-free
reconstructed velocity. -/
theorem finiteModeDiagonalLinear_spatialDivergence_zero_of_trace
    (lam : Fin 3 → ℝ) (htrace : ∑ i : Fin 3, lam i = 0) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeDiagonalLinearPolynomialMode i) y)
          (finiteModeDiagonalLinearCoefficientCurve lam)) t x = 0 := by
  intro t x
  rw [finiteModeDiagonalLinear_spatialDivergence_eq lam t x, htrace, mul_zero]

/-- Trace-free diagonal-linear velocity families simultaneously close the
finite-mode momentum equation through affine-quadratic pressure and remain
incompressible. -/
theorem finiteModeDiagonalLinear_traceFree_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    (ν ε : ℝ) (lam : Fin 3 → ℝ) (htrace : ∑ i : Fin 3, lam i = 0) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeDiagonalLinearPolynomialMode i) y)
              finiteModeAffineQuadraticPressureMode
              (finiteModeDiagonalLinearForcingCoefficients lam)
              (finiteModeDiagonalLinearCoefficientCurve lam) b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 := by
  rcases finiteModeDiagonalLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists
      ν ε lam with
    ⟨b, u, p, hu, hp, hres, hmom⟩
  refine ⟨b, u, p, hu, hp, hres, hmom, ?_⟩
  intro t x
  rw [hu]
  exact finiteModeDiagonalLinear_spatialDivergence_zero_of_trace lam htrace t x

/-- One off-diagonal symmetric trace-free linear mode:
`α (x₁ e₀ + x₀ e₁)`.  This is a positive counterpart to the shear obstruction:
the symmetric partner makes the pressure-closing gradient affine and curl-free. -/
def finiteModeSymmetricShearPolynomialMode (α : ℝ) (_ : PUnit) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j =>
    if j = (0 : Fin 3) then MvPolynomial.C α * MvPolynomial.X (1 : Fin 3)
    else if j = (1 : Fin 3) then MvPolynomial.C α * MvPolynomial.X (0 : Fin 3)
    else 0

/-- Component formula for the symmetric off-diagonal shear reconstruction. -/
theorem finiteModeSymmetricShear_reconstructedVelocity_apply
    (α : ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α i) y)
        finiteModeIdentityCoefficientCurve t x j =
      if j = (0 : Fin 3) then α * t * x (1 : Fin 3)
      else if j = (1 : Fin 3) then α * t * x (0 : Fin 3)
      else 0 := by
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeIdentityCoefficientCurve, finiteModeSymmetricShearPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul,
      mul_assoc] <;>
    ring

/-- Affine pressure matrix closing the symmetric off-diagonal shear mode. -/
def finiteModeSymmetricShearAffinePressureMatrix
    (α : ℝ) (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i = (0 : Fin 3) ∧ j = (0 : Fin 3) then -(α * α * (t * t))
    else if i = (1 : Fin 3) ∧ j = (1 : Fin 3) then -(α * α * (t * t))
    else if (i = (0 : Fin 3) ∧ j = (1 : Fin 3)) ∨
        (i = (1 : Fin 3) ∧ j = (0 : Fin 3)) then -α
    else 0

/-- The symmetric off-diagonal shear pressure matrix is symmetric. -/
theorem finiteModeSymmetricShearAffinePressureMatrix_symm
    (α : ℝ) (t : NSTime) :
    ∀ i j, finiteModeSymmetricShearAffinePressureMatrix α t i j =
      finiteModeSymmetricShearAffinePressureMatrix α t j i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteModeSymmetricShearAffinePressureMatrix]

/-- The affine-gradient form of the symmetric shear closing pressure gradient. -/
theorem finiteModeSymmetricShearAffineGradientField_eq
    (α : ℝ) (t : NSTime) (x : NSSpace) :
    finiteModeAffineGradientField 0
        (finiteModeSymmetricShearAffinePressureMatrix α t) x =
      fun j =>
        if j = (0 : Fin 3) then
          -(α * α * (t * t)) * x (0 : Fin 3) + (-α) * x (1 : Fin 3)
        else if j = (1 : Fin 3) then
          (-α) * x (0 : Fin 3) + -(α * α * (t * t)) * x (1 : Fin 3)
        else 0 := by
  ext j
  fin_cases j <;>
    simp [finiteModeAffineGradientField,
      finiteModeSymmetricShearAffinePressureMatrix, Fin.sum_univ_three]

/-- The computed closing pressure gradient for the symmetric off-diagonal shear
mode is affine with symmetric linear part. -/
theorem finiteModeSymmetricShearPolynomialClosingPressureGradient_affine_eq
    (ν α : ℝ) (t : NSTime) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν (finiteModeSymmetricShearPolynomialMode α)
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                (finiteModeSymmetricShearPolynomialMode α)
                finiteModeIdentityCoefficientCurve s))
          t) =
      finiteModeAffineGradientField 0
        (finiteModeSymmetricShearAffinePressureMatrix α t) := by
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
      finiteModeSymmetricShearPolynomialMode,
      finiteModeProjectedNSRHS,
      finiteModeUnitForcingCoefficients,
      finiteModeIdentityCoefficientCurve,
      finiteModeAffineGradientField,
      finiteModeSymmetricShearAffinePressureMatrix,
      finiteModePolynomialVectorFieldEval_apply,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.eval_mul] <;>
    ring

/-- The symmetric off-diagonal shear mode is divergence-free. -/
theorem finiteModeSymmetricShearPolynomialMode_spatialDivergence
    (α : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (fun _ : NSTime => fun y : NSSpace =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α PUnit.unit) y) t x = 0 := by
  unfold spatialDivergence spatialFDeriv
  change
    (∑ j : Fin 3,
      (fderiv ℝ
          (finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α PUnit.unit)) x
        (EuclideanSpace.single j (1 : ℝ))) j) = 0
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModeSymmetricShearPolynomialMode α PUnit.unit) x).fderiv]
  simp [finiteModeSymmetricShearPolynomialMode,
    finiteModePolynomialVectorFieldFDeriv_apply, Fin.sum_univ_three,
    MvPolynomial.pderiv_X]

/-- The reconstructed symmetric off-diagonal shear velocity is divergence-free
for every amplitude and time. -/
theorem finiteModeSymmetricShear_reconstructed_spatialDivergence_zero
    (α : ℝ) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeSymmetricShearPolynomialMode α i) y)
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  intro t x
  rw [finiteModeReconstructedVelocity_spatialDivergence
    (fun i y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeSymmetricShearPolynomialMode α i) y)
    finiteModeIdentityCoefficientCurve t x]
  · simp [finiteModeSymmetricShearPolynomialMode_spatialDivergence]
  · intro i
    cases i
    exact (finiteModePolynomialVectorFieldEval_hasFDerivAt
      (finiteModeSymmetricShearPolynomialMode α PUnit.unit) x).differentiableAt

/-- Positive off-diagonal instance: the symmetric trace-free shear mode admits
finite affine-quadratic pressure closure and remains divergence-free. -/
theorem finiteModeSymmetricShear_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    (ν ε α : ℝ) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
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
          ∀ t x, spatialDivergence u t x = 0 := by
  rcases
    finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
      ν (finiteModeSymmetricShearPolynomialMode α)
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve ε
      (fun t _ht => finiteModeIdentityCoefficientCurve_hasDerivAt t)
      (fun _ => 0)
      (finiteModeSymmetricShearAffinePressureMatrix α)
      (fun t _ht => finiteModeSymmetricShearAffinePressureMatrix_symm α t)
      (fun t _ht =>
        finiteModeSymmetricShearPolynomialClosingPressureGradient_affine_eq ν α t) with
    ⟨b, u, p, hu, hp, hres, hmom⟩
  refine ⟨b, u, p, hu, hp, hres, hmom, ?_⟩
  intro t x
  rw [hu]
  exact finiteModeSymmetricShear_reconstructed_spatialDivergence_zero α t x

end NavierStokes
end FluidDynamics
end Mettapedia
