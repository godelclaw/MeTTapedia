import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeLinearMatrixExamplesPart1

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

def finiteModeLinearMatrixTimeVelocity
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) : NSVelocityField :=
  finiteModeReconstructedVelocity
    (fun (i : PUnit.{1}) y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeLinearMatrixPolynomialMode A i) y)
    (finiteModeScalarAmplitudeCoefficientCurve g)

/-- Component formula for the time-dependent matrix-linear velocity. -/
theorem finiteModeLinearMatrixTimeVelocity_apply
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeLinearMatrixTimeVelocity A g t x j =
      g t * ∑ k : Fin 3, A j k * x k := by
  unfold finiteModeLinearMatrixTimeVelocity
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeScalarAmplitudeCoefficientCurve,
      finiteModeLinearMatrixPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul,
      Fin.sum_univ_three]

/-- Each time slice of `u(t,x)=g(t)A x` has the kinetic-energy density of the
linear map `(g(t))A`. -/
theorem kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) (t : NSTime) :
    kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t =
      finiteModeLinearMapKineticEnergyDensity ((g t) • finiteModeLinearMatrixCLM A) := by
  funext x
  have hvec :
      finiteModeLinearMatrixTimeVelocity A g t x =
        ((g t) • finiteModeLinearMatrixCLM A) x := by
    ext j
    rw [finiteModeLinearMatrixTimeVelocity_apply]
    simp [finiteModeLinearMatrixCLM_apply]
  simp [kineticEnergyDensity, finiteModeLinearMapKineticEnergyDensity, hvec]

/-- If the matrix mode is nonzero and the scalar amplitude is active at a time
slice, the corresponding kinetic-energy density is not integrable on `ℝ^3`. -/
theorem not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ} {t : NSTime}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg : g t ≠ 0) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t) := by
  intro hInt
  rw [kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity A g t] at hInt
  rcases hA with ⟨i, j, hij⟩
  have hL : finiteModeLinearMatrixCLM A ≠ 0 :=
    finiteModeLinearMatrixCLM_ne_zero_of_entry_ne hij
  have hsmul : (g t) • finiteModeLinearMatrixCLM A ≠ 0 := by
    intro hzero
    have hmap : finiteModeLinearMatrixCLM A = 0 := by
      ext x j
      have hcomp :=
        congrArg (fun L : NSSpace →L[ℝ] NSSpace => L x j) hzero
      simp at hcomp
      rcases hcomp with hgt | hcoord
      · exact (hg hgt).elim
      · simpa using hcoord
    exact hL hmap
  exact not_integrable_finiteModeLinearMapKineticEnergyDensity hsmul hInt

/-- A genuinely active matrix-linear time-dependent velocity cannot satisfy the
global bounded-energy predicate. -/
theorem not_boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg : ∃ t : NSTime, g t ≠ 0) :
    ¬ boundedKineticEnergy (finiteModeLinearMatrixTimeVelocity A g) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  rcases hg with ⟨t, hgt⟩
  exact not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity
    hA hgt (hbound t).1

/-- If `g(0) ≠ 0`, the initial datum associated to a nonzero matrix-linear
finite-mode velocity is not finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg0 : g 0 ≠ 0) :
    ¬ finiteInitialKineticEnergy (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) := by
  intro hE
  have hInt :
      MeasureTheory.Integrable
        (kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) 0) := by
    simpa [finiteInitialKineticEnergy, initialKineticEnergyDensity, kineticEnergyDensity] using hE
  exact not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity hA hg0 hInt

/-- The pressure matrix closing the time-dependent matrix-linear velocity
`u(t,x)=g(t) A x` when `g'(t)=gdot(t)`. -/
def finiteModeLinearMatrixTimePressureMatrix
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j => -(gdot t * A i j + g t * g t * finiteModeMatrixSquare A i j)

/-- Coefficients for the affine-quadratic pressure closing the time-dependent
matrix-linear velocity. -/
def finiteModeLinearMatrixTimePressureCoefficients
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ) :
    NSTime → FiniteModeState FiniteModeAffineQuadraticPressureIndex :=
  fun t =>
    finiteModeAffineQuadraticPressureCoefficientsAt
      (0 : NSSpace) (finiteModeLinearMatrixTimePressureMatrix A g gdot t)

/-- The affine-quadratic pressure field for the time-dependent matrix-linear
velocity. -/
def finiteModeLinearMatrixTimePressure
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ) : NSPressureField :=
  finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode
    (finiteModeLinearMatrixTimePressureCoefficients A g gdot)

/-- If `A` is symmetric, the time-dependent closing pressure matrix is
symmetric at every time. -/
theorem finiteModeLinearMatrixTimePressureMatrix_symm
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i) (t : NSTime) :
    ∀ i j, finiteModeLinearMatrixTimePressureMatrix A g gdot t i j =
      finiteModeLinearMatrixTimePressureMatrix A g gdot t j i := by
  intro i j
  simp [finiteModeLinearMatrixTimePressureMatrix, hA i j,
    finiteModeMatrixSquare_symm A hA i j]

/-- The time derivative of `u(t,x)=g(t) A x` is `gdot(t) A x`. -/
theorem finiteModeLinearMatrix_timeDependent_timeVelocityDerivative_eq
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    {t : NSTime} (hg : HasDerivAt g (gdot t) t) (x : NSSpace) :
    timeVelocityDerivative (finiteModeLinearMatrixTimeVelocity A g) t x =
      fun j => gdot t * ∑ k : Fin 3, A j k * x k := by
  unfold finiteModeLinearMatrixTimeVelocity
  rw [finiteModeReconstructedVelocity_timeDerivative_at
    (fun (i : PUnit.{1}) y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeLinearMatrixPolynomialMode A i) y)
    (finiteModeScalarForcingCoefficients (gdot t))
    (finiteModeScalarAmplitudeCoefficientCurve g) t
    (finiteModeScalarAmplitudeCoefficientCurve_hasDerivAt g gdot hg) x]
  ext j
  fin_cases j <;>
    simp [finiteModeReconstructedAcceleration, finiteModeReconstructedVelocity,
      finiteModeReconstructionCLM, finiteModeProjectedNSRHS,
      finiteModeScalarForcingCoefficients,
      finiteModeScalarAmplitudeCoefficientCurve,
      finiteModeLinearMatrixPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul,
      Fin.sum_univ_three]

/-- The convection term for `u(t,x)=g(t) A x` is `g(t)^2 A^2 x`. -/
theorem finiteModeLinearMatrix_timeDependent_spatialConvection_eq
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialConvection (finiteModeLinearMatrixTimeVelocity A g) t x =
      fun j => (g t * g t) * ∑ k : Fin 3,
        finiteModeMatrixSquare A j k * x k := by
  unfold finiteModeLinearMatrixTimeVelocity
  rw [finiteModePolynomialReconstructedVelocity_spatialConvection
    (finiteModeLinearMatrixPolynomialMode A)
    (finiteModeScalarAmplitudeCoefficientCurve g) t x]
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialConvectionComponents,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeLinearMatrixPolynomialMode,
      finiteModeScalarAmplitudeCoefficientCurve,
      finiteModeMatrixSquare,
      finiteModePolynomialVectorFieldEval_apply, Fin.sum_univ_three,
      MvPolynomial.pderiv_X, Pi.single_apply, MvPolynomial.eval_mul] <;>
    ring_nf

/-- The matrix-linear time-dependent velocity has zero spatial Laplacian. -/
theorem finiteModeLinearMatrix_timeDependent_spatialLaplacian_zero
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian (finiteModeLinearMatrixTimeVelocity A g) t x = 0 := by
  unfold finiteModeLinearMatrixTimeVelocity
  rw [finiteModePolynomialReconstructedVelocity_spatialLaplacian
    (finiteModeLinearMatrixPolynomialMode A)
    (finiteModeScalarAmplitudeCoefficientCurve g) t x]
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialLaplacianComponents,
      finiteModePolynomialScalarLaplacian,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeLinearMatrixPolynomialMode,
      finiteModeScalarAmplitudeCoefficientCurve,
      finiteModePolynomialVectorFieldEval_apply, Fin.sum_univ_three,
      MvPolynomial.pderiv_X, Pi.single_apply]

/-- The divergence of `u(t,x)=g(t) A x` is `g(t) trace(A)`. -/
theorem finiteModeLinearMatrix_timeDependent_spatialDivergence_eq
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialDivergence (finiteModeLinearMatrixTimeVelocity A g) t x =
      g t * ∑ i : Fin 3, A i i := by
  unfold finiteModeLinearMatrixTimeVelocity
  rw [finiteModeReconstructedVelocity_spatialDivergence
    (fun (i : PUnit.{1}) y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeLinearMatrixPolynomialMode A i) y)
    (finiteModeScalarAmplitudeCoefficientCurve g) t x]
  · rw [Fintype.sum_eq_single PUnit.unit]
    rw [finiteModeLinearMatrixPolynomialMode_spatialDivergence]
    simp [finiteModeScalarAmplitudeCoefficientCurve]
    intro i hi
    cases i
    exact (hi rfl).elim
  · intro i
    cases i
    exact (finiteModePolynomialVectorFieldEval_hasFDerivAt
      (finiteModeLinearMatrixPolynomialMode A PUnit.unit) x).differentiableAt

/-- Trace-free time-dependent matrix-linear velocities are divergence-free. -/
theorem finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (htrace : ∑ i : Fin 3, A i i = 0) :
    ∀ t x, spatialDivergence (finiteModeLinearMatrixTimeVelocity A g) t x = 0 := by
  intro t x
  rw [finiteModeLinearMatrix_timeDependent_spatialDivergence_eq A g t x,
    htrace, mul_zero]

/-- The explicit affine-quadratic pressure has gradient
`-(gdot(t) A + g(t)^2 A^2)x`. -/
theorem finiteModeLinearMatrix_timeDependent_pressureGradient_eq
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (finiteModeLinearMatrixTimePressure A g gdot) t x =
      finiteModeAffineGradientField (0 : NSSpace)
        (finiteModeLinearMatrixTimePressureMatrix A g gdot t) x := by
  unfold finiteModeLinearMatrixTimePressure
  rw [finiteModeReconstructedPressure_spatialPressureGradient
    finiteModeAffineQuadraticPressureMode
    (finiteModeLinearMatrixTimePressureCoefficients A g gdot) t x
    (fun k => finiteModeAffineQuadraticPressureMode_differentiableAt k x)]
  change
    finiteModePressureGradientSynthesis finiteModeAffineQuadraticPressureMode
        (finiteModeAffineQuadraticPressureCoefficientsAt (0 : NSSpace)
          (finiteModeLinearMatrixTimePressureMatrix A g gdot t)) x =
      finiteModeAffineGradientField (0 : NSSpace)
        (finiteModeLinearMatrixTimePressureMatrix A g gdot t) x
  rw [finiteModeAffineQuadraticPressureGradientSynthesis
    (0 : NSSpace) (finiteModeLinearMatrixTimePressureMatrix A g gdot t)
    (finiteModeLinearMatrixTimePressureMatrix_symm A g gdot hA t) x]

/-- Smooth scalar amplitudes give smooth time-dependent matrix-linear
velocities. -/
theorem finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) :
    smoothSpaceTimeVelocity (finiteModeLinearMatrixTimeVelocity A g) := by
  unfold finiteModeLinearMatrixTimeVelocity
  exact
    finiteModeReconstructedVelocity_smoothSpaceTime
      (fun (i : PUnit.{1}) y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeLinearMatrixPolynomialMode A i) y)
      (finiteModeScalarAmplitudeCoefficientCurve g)
      (fun i => by
        cases i
        simpa [finiteModeScalarAmplitudeCoefficientCurve] using hg)
      (fun i => by
        cases i
        exact finiteModePolynomialVectorFieldEval_contDiff_top
          (finiteModeLinearMatrixPolynomialMode A (PUnit.unit : PUnit.{1})))

/-- The time-dependent pressure coefficients are smooth when `g` and `gdot`
are smooth. -/
theorem finiteModeLinearMatrixTimePressureCoefficients_contDiff
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot) :
    ∀ k, ContDiff ℝ ∞
      (fun t : NSTime => finiteModeLinearMatrixTimePressureCoefficients A g gdot t k) := by
  intro k
  rcases k with j | k
  · simpa [finiteModeLinearMatrixTimePressureCoefficients,
      finiteModeAffineQuadraticPressureCoefficientsAt] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
  · rcases k with j | r
    · have h1 : ContDiff ℝ ∞ (fun t : NSTime => gdot t * A j j) :=
        hgdot.mul contDiff_const
      have h2a : ContDiff ℝ ∞ (fun t : NSTime => g t * g t) :=
        hg.mul hg
      have h2 : ContDiff ℝ ∞
          (fun t : NSTime => g t * g t * finiteModeMatrixSquare A j j) :=
        h2a.mul contDiff_const
      simpa [finiteModeLinearMatrixTimePressureCoefficients,
        finiteModeAffineQuadraticPressureCoefficientsAt,
        finiteModeLinearMatrixTimePressureMatrix] using (h1.add h2).neg
    · let i₀ : Fin 3 := (finiteModeOffDiagonalPair r).1
      let i₁ : Fin 3 := (finiteModeOffDiagonalPair r).2
      have h1 : ContDiff ℝ ∞ (fun t : NSTime => gdot t * A i₀ i₁) :=
        hgdot.mul contDiff_const
      have h2a : ContDiff ℝ ∞ (fun t : NSTime => g t * g t) :=
        hg.mul hg
      have h2 : ContDiff ℝ ∞
          (fun t : NSTime => g t * g t * finiteModeMatrixSquare A i₀ i₁) :=
        h2a.mul contDiff_const
      simpa [finiteModeLinearMatrixTimePressureCoefficients,
        finiteModeAffineQuadraticPressureCoefficientsAt,
        finiteModeLinearMatrixTimePressureMatrix, i₀, i₁] using (h1.add h2).neg

/-- Smooth amplitudes and derivative data give a smooth explicit
affine-quadratic pressure for the time-dependent matrix-linear velocity. -/
theorem finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot) :
    smoothSpaceTimePressure (finiteModeLinearMatrixTimePressure A g gdot) := by
  unfold finiteModeLinearMatrixTimePressure
  exact
    finiteModeReconstructedPressure_smoothSpaceTime
      finiteModeAffineQuadraticPressureMode
      (finiteModeLinearMatrixTimePressureCoefficients A g gdot)
      (finiteModeLinearMatrixTimePressureCoefficients_contDiff A g gdot hg hgdot)
      finiteModeAffineQuadraticPressureMode_contDiff

/-- Direct pointwise momentum identity for the global-in-time
time-dependent matrix-linear reconstruction.  The construction is global in
time, but it is only a polynomial finite-mode PDE identity; it does not assert
finite-energy Clay admissibility. -/
theorem finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (hg : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∀ t x,
      timeVelocityDerivative (finiteModeLinearMatrixTimeVelocity A g) t x +
          spatialConvection (finiteModeLinearMatrixTimeVelocity A g) t x +
            spatialPressureGradient (finiteModeLinearMatrixTimePressure A g gdot) t x =
        ν • spatialLaplacian (finiteModeLinearMatrixTimeVelocity A g) t x := by
  intro t x
  ext j
  have htime := congrFun
    (finiteModeLinearMatrix_timeDependent_timeVelocityDerivative_eq A g gdot
      (hg t) x) j
  have hconv := congrFun
    (finiteModeLinearMatrix_timeDependent_spatialConvection_eq A g t x) j
  have hpress :
      (spatialPressureGradient
        (finiteModeLinearMatrixTimePressure A g gdot) t x).ofLp j =
        (finiteModeAffineGradientField (0 : NSSpace)
          (finiteModeLinearMatrixTimePressureMatrix A g gdot t) x).ofLp j := by
    exact congrArg (fun v : NSSpace => v.ofLp j)
      (finiteModeLinearMatrix_timeDependent_pressureGradient_eq A g gdot hA t x)
  have hlap :
      (spatialLaplacian (finiteModeLinearMatrixTimeVelocity A g) t x).ofLp j =
        (0 : NSSpace).ofLp j := by
    exact congrArg (fun v : NSSpace => v.ofLp j)
      (finiteModeLinearMatrix_timeDependent_spatialLaplacian_zero A g t x)
  simp only [PiLp.add_apply, PiLp.smul_apply]
  rw [htime, hconv, hpress, hlap]
  fin_cases j <;>
    simp [finiteModeAffineGradientField,
      finiteModeLinearMatrixTimePressureMatrix,
      finiteModeMatrixSquare, Fin.sum_univ_three] <;>
    ring_nf

/-- Global-in-time time-dependent positive construction: for any symmetric
trace-free matrix `A` and differentiable scalar amplitude `g`, the field
`u(t,x)=g(t) A x` admits an explicit finite affine-quadratic pressure making the
pointwise momentum equation and incompressibility hold for all times. -/
theorem finiteModeLinearMatrix_timeDependent_global_momentum_incompressible_exists
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hg : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            (∀ t x,
              timeVelocityDerivative u t x +
                  spatialConvection u t x +
                    spatialPressureGradient p t x =
                ν • spatialLaplacian u t x) ∧
            ∀ t x, spatialDivergence u t x = 0 := by
  refine
    ⟨finiteModeLinearMatrixTimePressureCoefficients A g gdot,
      finiteModeLinearMatrixTimeVelocity A g,
      finiteModeLinearMatrixTimePressure A g gdot,
      rfl, rfl, rfl, ?_, ?_⟩
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
        ν A g gdot hA hg
  · exact finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
      A g htrace

/-- Smooth global-in-time finite-mode regularity package for the
time-dependent matrix-linear construction.  It gives smooth velocity and
pressure together with the pointwise PDE identities; it still makes no
bounded-energy assertion, since nonzero linear fields on `ℝ^3` are not
finite-energy. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_exists
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot)
    (hderiv : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            smoothSpaceTimeVelocity u ∧
              smoothSpaceTimePressure p ∧
                (∀ t x,
                  timeVelocityDerivative u t x +
                      spatialConvection u t x +
                        spatialPressureGradient p t x =
                    ν • spatialLaplacian u t x) ∧
                ∀ t x, spatialDivergence u t x = 0 := by
  refine
    ⟨finiteModeLinearMatrixTimePressureCoefficients A g gdot,
      finiteModeLinearMatrixTimeVelocity A g,
      finiteModeLinearMatrixTimePressure A g gdot,
      rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity A g hg
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure
        A g gdot hg hgdot
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
        ν A g gdot hA hderiv
  · exact finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
      A g htrace

/-- The same smooth global-in-time matrix-linear construction, paired with the
honest whole-space obstruction: if the matrix has a nonzero entry and the
amplitude is nonzero at some time, the constructed velocity cannot satisfy the
concrete bounded kinetic-energy predicate. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_without_boundedEnergy_exists
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hAnz : ∃ i j : Fin 3, A i j ≠ 0)
    (hgnz : ∃ t : NSTime, g t ≠ 0)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot)
    (hderiv : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            smoothSpaceTimeVelocity u ∧
              smoothSpaceTimePressure p ∧
                (∀ t x,
                  timeVelocityDerivative u t x +
                      spatialConvection u t x +
                        spatialPressureGradient p t x =
                    ν • spatialLaplacian u t x) ∧
                (∀ t x, spatialDivergence u t x = 0) ∧
                  ¬ boundedKineticEnergy u := by
  refine
    ⟨finiteModeLinearMatrixTimePressureCoefficients A g gdot,
      finiteModeLinearMatrixTimeVelocity A g,
      finiteModeLinearMatrixTimePressure A g gdot,
      rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity A g hg
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure
        A g gdot hg hgdot
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
        ν A g gdot hA hderiv
  · exact finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
      A g htrace
  · exact not_boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity hAnz hgnz

end NavierStokes
end FluidDynamics
end Mettapedia
