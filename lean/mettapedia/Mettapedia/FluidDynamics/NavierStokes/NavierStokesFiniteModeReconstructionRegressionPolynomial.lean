import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeReconstructionRegressionCore

/-!
# Polynomial Regression Tests for Finite-Mode Reconstruction

This module checks homogeneous polynomial primitives, polynomial vector-field
evaluation, polynomial pressure gradients, and one-mode polynomial closure.
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

/-- Homogeneous curl-free polynomial vector fields have the radial polynomial
pressure primitive promised by the pressure reconstruction algebra. -/
theorem finiteModeHomogeneousPolynomialPressurePrimitive_pderiv_regression
    (n : ℕ) (F : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ j, (F j).IsHomogeneous n)
    (hcurl : ∀ i j, MvPolynomial.pderiv i (F j) =
      MvPolynomial.pderiv j (F i))
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeHomogeneousPolynomialPressurePrimitive n F) =
      F j :=
  finiteModeHomogeneousPolynomialPressurePrimitive_pderiv n F hhom hcurl j

/-- Finite homogeneous polynomial decompositions reconstruct pressure
primitives componentwise. -/
theorem finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv_regression
    (s : Finset ℕ) (F : ℕ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ n ∈ s, ∀ j, (F n j).IsHomogeneous n)
    (hcurl : ∀ n ∈ s, ∀ i j,
      MvPolynomial.pderiv i (F n j) =
        MvPolynomial.pderiv j (F n i))
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeFiniteHomogeneousPolynomialPressurePrimitive s F) =
      s.sum fun n => F n j :=
  finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv
    s F hhom hcurl j

/-- Coefficients of formal partial derivatives are shifted by one exponent in
the differentiated coordinate. -/
theorem finiteModePolynomial_coeff_pderiv_regression
    (i : Fin 3) (d : Fin 3 →₀ ℕ) (φ : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.coeff d (MvPolynomial.pderiv i φ) =
      MvPolynomial.coeff (d + Finsupp.single i 1) φ *
        ((d i + 1 : ℕ) : ℝ) :=
  finiteModePolynomial_coeff_pderiv i d φ

/-- Partial differentiation commutes with homogeneous projection up to the
expected degree shift. -/
theorem finiteModeHomogeneousComponent_pderiv_succ_regression
    (n : ℕ) (i : Fin 3) (φ : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent (n + 1) φ) =
      MvPolynomial.homogeneousComponent n (MvPolynomial.pderiv i φ) :=
  finiteModeHomogeneousComponent_pderiv_succ n i φ

/-- General curl-free polynomial vector fields have an explicit polynomial
pressure primitive. -/
theorem finiteModePolynomialPressurePrimitive_pderiv_regression
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (j : Fin 3) :
    MvPolynomial.pderiv j (finiteModePolynomialPressurePrimitive G) =
      G j :=
  finiteModePolynomialPressurePrimitive_pderiv G hcurl j

/-- Formal mixed partial derivatives commute for polynomial pressure
potentials. -/
theorem finiteModePolynomial_pderiv_comm_regression
    (i j : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) :=
  finiteModePolynomial_pderiv_comm i j p

/-- Curl-freeness is exactly the polynomial pressure-solvability condition. -/
theorem finiteModePolynomialPressurePrimitive_exists_iff_curlFree_regression
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∃ p : MvPolynomial (Fin 3) ℝ,
        ∀ j, MvPolynomial.pderiv j p = G j) ↔
      ∀ i j, MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i) :=
  finiteModePolynomialPressurePrimitive_exists_iff_curlFree G

/-- Evaluating a multivariate polynomial on `NSSpace` has the expected
coordinate-gradient formula. -/
theorem finiteModePolynomialEval_gradient_regression
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    gradient (fun y : NSSpace => MvPolynomial.eval y p) x =
      finiteModePolynomialEvalGradient p x :=
  finiteModePolynomialEval_gradient p x

/-- Scalar polynomial evaluation has the formal polynomial Laplacian. -/
theorem finiteModePolynomialEval_laplacian_regression
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    Δ (fun y : NSSpace => MvPolynomial.eval y p) x =
      MvPolynomial.eval x (finiteModePolynomialScalarLaplacian p) :=
  finiteModePolynomialEval_laplacian p x

/-- Polynomial vector fields have the expected componentwise Fréchet
derivative. -/
theorem finiteModePolynomialVectorFieldEval_hasFDerivAt_regression
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasFDerivAt (finiteModePolynomialVectorFieldEval U)
      (finiteModePolynomialVectorFieldFDeriv U x) x :=
  finiteModePolynomialVectorFieldEval_hasFDerivAt U x

/-- A one-mode polynomial finite-mode velocity reconstruction is represented by
the explicit polynomial linear combination of its mode components. -/
theorem oneModePolynomialReconstructedVelocity_eq_eval_regression
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedVelocityComponents modePoly a t) x :=
  finiteModePolynomialReconstructedVelocity_eq_eval modePoly a t x

/-- A one-mode projected acceleration from polynomial spatial modes is
represented by its explicit polynomial linear combination. -/
theorem oneModePolynomialReconstructedAcceleration_eq_eval_regression
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedAccelerationComponents modePoly C a t) x :=
  finiteModePolynomialReconstructedAcceleration_eq_eval modePoly C a t x

/-- Concrete convection of a polynomial vector field matches the formal
component formula `Σ_r u_r ∂_r u_j`. -/
theorem finiteModePolynomialVectorField_spatialConvection_regression
    (U : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (fun s y => finiteModePolynomialVectorFieldEval (U s) y) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialConvectionComponents (U t)) x :=
  finiteModePolynomialVectorField_spatialConvection U t x

/-- Concrete spatial Laplacian of a polynomial vector field matches the formal
componentwise polynomial Laplacian. -/
theorem finiteModePolynomialVectorField_spatialLaplacian_regression
    (U : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (fun s y => finiteModePolynomialVectorFieldEval (U s) y) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialLaplacianComponents (U t)) x :=
  finiteModePolynomialVectorField_spatialLaplacian U t x

/-- The concrete convection of a one-mode polynomial finite-mode
reconstruction is represented by the formal polynomial convection of the
reconstructed velocity components. -/
theorem oneModePolynomialReconstructedVelocity_spatialConvection_regression
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity
          (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialConvectionComponents
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t)) x :=
  finiteModePolynomialReconstructedVelocity_spatialConvection modePoly a t x

/-- The concrete spatial Laplacian of a one-mode polynomial reconstruction is
represented by the formal componentwise polynomial Laplacian. -/
theorem oneModePolynomialReconstructedVelocity_spatialLaplacian_regression
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialLaplacianComponents
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t)) x :=
  finiteModePolynomialReconstructedVelocity_spatialLaplacian modePoly a t x

/-- With a polynomial Laplacian representation supplied, the full one-mode
non-pressure finite-mode defect is represented by the explicit polynomial
defect components. -/
theorem oneModePolynomialNonPressureDefect_eq_eval_of_laplacian_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (lapPoly : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hLap : ∀ t x,
      spatialLaplacian
          (finiteModeReconstructedVelocity
            (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
        finiteModePolynomialVectorFieldEval (lapPoly t) x)
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialNonPressureDefectComponents ν modePoly C a lapPoly t) x :=
  finiteModePolynomialNonPressureDefect_eq_eval_of_laplacian
    ν modePoly C a lapPoly hLap t x

/-- The full one-mode polynomial non-pressure finite-mode defect is represented
by the explicit polynomial defect components with the formal Laplacian. -/
theorem oneModePolynomialNonPressureDefect_eq_eval_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialNonPressureDefectComponents ν modePoly C a
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents modePoly a s)) t) x :=
  finiteModePolynomialNonPressureDefect_eq_eval ν modePoly C a t x

/-- The formal polynomial pressure primitive reconstructs a concrete spatial
pressure gradient for any curl-free polynomial vector field. -/
theorem finiteModePolynomialPressureMode_gradient_regression
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (x : NSSpace) :
    gradient (finiteModePolynomialPressureMode G) x =
      finiteModePolynomialVectorFieldEval G x :=
  finiteModePolynomialPressureMode_gradient G hcurl x

/-- The same polynomial pressure solve through the Navier-Stokes
`spatialPressureGradient` API. -/
theorem finiteModePolynomialPressureMode_spatialPressureGradient_regression
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ y => finiteModePolynomialPressureMode G y) t x =
      finiteModePolynomialVectorFieldEval G x :=
  finiteModePolynomialPressureMode_spatialPressureGradient G hcurl t x

/-- Pointwise equality of a polynomial pressure gradient with a polynomial
vector field is equivalent to coefficient-level derivative identities. -/
theorem finiteModePolynomialPressureGradient_eq_eval_iff_pderiv_regression
    (p : MvPolynomial (Fin 3) ℝ)
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) :
    (∀ x : NSSpace,
      spatialPressureGradient (fun _ y => MvPolynomial.eval y p) t x =
        finiteModePolynomialVectorFieldEval G x) ↔
      ∀ j, MvPolynomial.pderiv j p = G j :=
  finiteModePolynomialPressureGradient_eq_eval_iff_pderiv p G t

/-- Time-dependent version of the polynomial pressure-gradient coefficient
equivalence. -/
theorem finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv_regression
    (P : NSTime → MvPolynomial (Fin 3) ℝ)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∀ t x,
      spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
        finiteModePolynomialVectorFieldEval (G t) x) ↔
      ∀ t j, MvPolynomial.pderiv j (P t) = G t j :=
  finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv P G

/-- Time-dependent polynomial pressure-gradient solvability is exactly the
curl-free condition on each polynomial time slice. -/
theorem finiteModeTimePolynomialPressureGradient_exists_iff_curlFree_regression
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t x,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            finiteModePolynomialVectorFieldEval (G t) x) ↔
      ∀ t i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) :=
  finiteModeTimePolynomialPressureGradient_exists_iff_curlFree G

/-- On any time set, a polynomial pressure closes a polynomially represented
non-pressure defect exactly when that polynomial defect is curl-free. -/
theorem oneModePolynomialPressure_closes_nonPressureDefectOn_iff_curlFree_of_polynomialDefect_regression
    (I : Set NSTime)
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hdefect : ∀ t ∈ I,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ I, ∀ x : NSSpace,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            -finiteModeNonPressureMomentumDefect ν mode C a t x) ↔
      ∀ t ∈ I, ∀ i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) :=
  finiteModePolynomialPressure_closes_nonPressureDefectOn_iff_curlFree_of_polynomialDefect
    I ν mode C a G hdefect

end FiniteModeReconstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
