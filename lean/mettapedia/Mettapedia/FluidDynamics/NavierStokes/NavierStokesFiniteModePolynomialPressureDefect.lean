import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressureEvaluation

/-!
# Finite-mode polynomial reconstructed defects
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

/-- Polynomial vector field components for a finite-mode reconstructed velocity
when each selected spatial mode is represented by polynomial components. -/
def finiteModePolynomialReconstructedVelocityComponents
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => ∑ i : ι, MvPolynomial.C (a t i) * modePoly i j

/-- The projected-RHS acceleration reconstructed from polynomial spatial modes
is again represented componentwise by an explicit polynomial vector field. -/
def finiteModePolynomialReconstructedAccelerationComponents
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => ∑ i : ι,
    MvPolynomial.C (finiteModeProjectedNSRHS C (a t) i) * modePoly i j

/-- Polynomial components for the convection term `(u · ∇)u`. -/
def finiteModePolynomialConvectionComponents
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => ∑ r : Fin 3, U r * MvPolynomial.pderiv r (U j)

/-- Polynomial components for the spatial Laplacian `Δu`. -/
def finiteModePolynomialLaplacianComponents
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => finiteModePolynomialScalarLaplacian (U j)

/-- Formal polynomial components for the non-pressure finite-mode momentum
defect.  The acceleration and convection pieces are computed from the
polynomial mode data; `lapPoly` records the polynomial representation of the
actual spatial Laplacian slice. -/
def finiteModePolynomialNonPressureDefectComponents
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (lapPoly : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j =>
    finiteModePolynomialReconstructedAccelerationComponents modePoly C a t j +
      finiteModePolynomialConvectionComponents
        (finiteModePolynomialReconstructedVelocityComponents modePoly a t) j -
        MvPolynomial.C ν * lapPoly t j

/-- The polynomial vector field that a pressure gradient must equal in order to
close the non-pressure finite-mode defect. -/
def finiteModePolynomialClosingPressureGradientComponents
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (lapPoly : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => -finiteModePolynomialNonPressureDefectComponents ν modePoly C a lapPoly t j

/-- If each selected finite mode is represented by polynomial components, then
the reconstructed velocity slice is represented by the corresponding polynomial
linear combination. -/
theorem finiteModePolynomialReconstructedVelocity_eq_eval
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedVelocityComponents modePoly a t) x := by
  ext j
  simp [finiteModePolynomialReconstructedVelocityComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- If each selected finite mode is represented by polynomial components, then
the projected acceleration slice is represented by the corresponding polynomial
linear combination. -/
theorem finiteModePolynomialReconstructedAcceleration_eq_eval
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedAccelerationComponents modePoly C a t) x := by
  ext j
  simp [finiteModePolynomialReconstructedAccelerationComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- Concrete convection of a polynomial vector field is the formal polynomial
vector field with components `Σ_r u_r ∂_r u_j`. -/
theorem finiteModePolynomialVectorField_spatialConvection
    (U : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (fun s y => finiteModePolynomialVectorFieldEval (U s) y) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialConvectionComponents (U t)) x := by
  unfold spatialConvection spatialFDeriv
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt (U t) x).fderiv]
  ext j
  simp [finiteModePolynomialConvectionComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- The concrete convection term for a finite-mode reconstruction from
polynomial spatial modes is represented by the formal polynomial convection of
the reconstructed polynomial velocity components. -/
theorem finiteModePolynomialReconstructedVelocity_spatialConvection
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity
          (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialConvectionComponents
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t)) x := by
  unfold spatialConvection spatialFDeriv
  have hslice :
      (fun y : NSSpace =>
        finiteModeReconstructedVelocity
          (fun i z => finiteModePolynomialVectorFieldEval (modePoly i) z) a t y) =
        finiteModePolynomialVectorFieldEval
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t) := by
    funext y
    exact finiteModePolynomialReconstructedVelocity_eq_eval modePoly a t y
  rw [hslice]
  rw [finiteModePolynomialReconstructedVelocity_eq_eval modePoly a t x]
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModePolynomialReconstructedVelocityComponents modePoly a t) x).fderiv]
  ext j
  simp [finiteModePolynomialConvectionComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- Concrete spatial Laplacian of a polynomial vector field is the formal
componentwise polynomial Laplacian. -/
theorem finiteModePolynomialVectorField_spatialLaplacian
    (U : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (fun s y => finiteModePolynomialVectorFieldEval (U s) y) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialLaplacianComponents (U t)) x := by
  unfold spatialLaplacian
  ext j
  have hproj :
      Δ ((EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) ∘
          finiteModePolynomialVectorFieldEval (U t)) x =
        (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)
          (Δ (finiteModePolynomialVectorFieldEval (U t)) x) := by
    simpa [Function.comp] using
      ((finiteModePolynomialVectorFieldEval_contDiff (U t)).contDiffAt
        (x := x)).laplacian_CLM_comp_left
          (l := (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ))
  change (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)
      (Δ (finiteModePolynomialVectorFieldEval (U t)) x) =
    (finiteModePolynomialVectorFieldEval
      (finiteModePolynomialLaplacianComponents (U t)) x) j
  rw [← hproj]
  rw [show ((EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) ∘
      finiteModePolynomialVectorFieldEval (U t)) =
        (fun y : NSSpace => MvPolynomial.eval y ((U t) j)) by
    funext y
    simp [Function.comp, finiteModePolynomialVectorFieldEval_apply]]
  simpa [finiteModePolynomialVectorFieldEval_apply,
    finiteModePolynomialLaplacianComponents] using
      finiteModePolynomialEval_laplacian ((U t) j) x

/-- The concrete spatial Laplacian of a finite-mode reconstruction from
polynomial spatial modes is represented by the formal componentwise polynomial
Laplacian of the reconstructed polynomial velocity components. -/
theorem finiteModePolynomialReconstructedVelocity_spatialLaplacian
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialLaplacianComponents
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t)) x := by
  rw [show finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a =
      fun s y => finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedVelocityComponents modePoly a s) y by
    funext s y
    exact finiteModePolynomialReconstructedVelocity_eq_eval modePoly a s y]
  exact finiteModePolynomialVectorField_spatialLaplacian
    (fun s => finiteModePolynomialReconstructedVelocityComponents modePoly a s) t x

/-- Once the Laplacian slice of a polynomial finite-mode reconstruction is
itself represented by polynomial components, the whole non-pressure momentum
defect is represented by the explicit polynomial expression above. -/
theorem finiteModePolynomialNonPressureDefect_eq_eval_of_laplacian
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
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
        (finiteModePolynomialNonPressureDefectComponents ν modePoly C a lapPoly t) x := by
  unfold finiteModeNonPressureMomentumDefect
  rw [finiteModePolynomialReconstructedAcceleration_eq_eval modePoly C a t x,
    finiteModePolynomialReconstructedVelocity_spatialConvection modePoly a t x,
    hLap t x]
  ext j
  simp [finiteModePolynomialNonPressureDefectComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- For polynomial spatial modes, the non-pressure finite-mode momentum defect
has an explicit polynomial representative with no external Laplacian
representation hypothesis. -/
theorem finiteModePolynomialNonPressureDefect_eq_eval
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialNonPressureDefectComponents ν modePoly C a
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents modePoly a s)) t) x := by
  exact finiteModePolynomialNonPressureDefect_eq_eval_of_laplacian
    ν modePoly C a
    (fun s => finiteModePolynomialLaplacianComponents
      (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
    (fun s y => finiteModePolynomialReconstructedVelocity_spatialLaplacian modePoly a s y)
    t x


end NavierStokes
end FluidDynamics
end Mettapedia
