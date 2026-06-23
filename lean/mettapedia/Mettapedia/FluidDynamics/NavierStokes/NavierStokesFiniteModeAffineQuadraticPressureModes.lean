import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeShearAccelerationObstruction

/-!
# Affine and quadratic finite-mode pressure basis.

This module contains the reusable pressure modes and gradient-synthesis facts.
Closure, obstruction, and concrete reconstruction examples live in downstream
modules.
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

/-- Mixed quadratic pressure mode `x ↦ x_i * x_j`. -/
def finiteModeMixedQuadraticPressureMode (i j : Fin 3) : NSSpace → ℝ :=
  fun x => x i * x j

/-- Mixed quadratic pressure modes are smooth. -/
theorem finiteModeMixedQuadraticPressureMode_contDiff
    (i j : Fin 3) :
    ContDiff ℝ ∞ (finiteModeMixedQuadraticPressureMode i j) := by
  unfold finiteModeMixedQuadraticPressureMode
  have hi : ContDiff ℝ ∞ (fun x : NSSpace => x i) := by
    simpa using (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).contDiff
  have hj : ContDiff ℝ ∞ (fun x : NSSpace => x j) := by
    simpa using (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).contDiff
  exact hi.mul hj

/-- Mixed quadratic pressure modes are differentiable. -/
theorem finiteModeMixedQuadraticPressureMode_differentiableAt
    (i j : Fin 3) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModeMixedQuadraticPressureMode i j) x := by
  unfold finiteModeMixedQuadraticPressureMode
  exact
    (finiteModeCoordinatePressureMode_differentiableAt i x).mul
      (finiteModeCoordinatePressureMode_differentiableAt j x)

/-- The gradient of `x ↦ x_i * x_j` is `x_j e_i + x_i e_j`. -/
theorem finiteModeMixedQuadraticPressureMode_gradient
    (i j : Fin 3) (x : NSSpace) :
    gradient (finiteModeMixedQuadraticPressureMode i j) x =
      x j • EuclideanSpace.single i (1 : ℝ) +
        x i • EuclideanSpace.single j (1 : ℝ) := by
  unfold finiteModeMixedQuadraticPressureMode gradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace)
          (x j • EuclideanSpace.single i (1 : ℝ) +
            x i • EuclideanSpace.single j (1 : ℝ)) =
        (x j) • (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ) +
          (x i) • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) := by
    ext y
    rw [ContinuousLinearMap.add_apply]
    rw [InnerProductSpace.toDual_apply_apply]
    simp [inner_add_left, inner_smul_left, EuclideanSpace.inner_single_left,
      add_comm]
  rw [hdual]
  have hi : HasFDerivAt (fun y : NSSpace => y i)
      (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ) x := by
    exact (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt
  have hj : HasFDerivAt (fun y : NSSpace => y j)
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) x := by
    exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).hasFDerivAt
  simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hi.mul hj

/-- Finite pressure basis for affine gradient fields: coordinate-linear
pressures, diagonal quadratics, and the three off-diagonal mixed quadratics. -/
abbrev FiniteModeAffineQuadraticPressureIndex :=
  Fin 3 ⊕ (Fin 3 ⊕ Fin 3)

/-- Decode the three off-diagonal quadratic modes as `(0,1)`, `(0,2)`,
and `(1,2)`. -/
def finiteModeOffDiagonalPair : Fin 3 → Fin 3 × Fin 3
  | 0 => ((0 : Fin 3), (1 : Fin 3))
  | 1 => ((0 : Fin 3), (2 : Fin 3))
  | 2 => ((1 : Fin 3), (2 : Fin 3))

/-- The concrete affine-quadratic pressure basis on `ℝ^3`. -/
def finiteModeAffineQuadraticPressureMode :
    FiniteModeAffineQuadraticPressureIndex → NSSpace → ℝ
  | Sum.inl j => finiteModeCoordinatePressureMode j
  | Sum.inr (Sum.inl j) => finiteModeDiagonalQuadraticPressureMode j
  | Sum.inr (Sum.inr r) =>
      finiteModeMixedQuadraticPressureMode
        (finiteModeOffDiagonalPair r).1 (finiteModeOffDiagonalPair r).2

/-- Every affine-quadratic pressure basis mode is smooth. -/
theorem finiteModeAffineQuadraticPressureMode_contDiff
    (k : FiniteModeAffineQuadraticPressureIndex) :
    ContDiff ℝ ∞ (finiteModeAffineQuadraticPressureMode k) := by
  rcases k with j | k
  · exact finiteModeCoordinatePressureMode_contDiff j
  · rcases k with j | r
    · exact finiteModeDiagonalQuadraticPressureMode_contDiff j
    · exact finiteModeMixedQuadraticPressureMode_contDiff
        (finiteModeOffDiagonalPair r).1 (finiteModeOffDiagonalPair r).2

/-- Coefficients for the affine-quadratic pressure basis.  The intended linear
part `A` is symmetric; off-diagonal modes use the upper-triangular entries. -/
def finiteModeAffineQuadraticPressureCoefficientsAt
    (c : NSSpace) (A : Fin 3 → Fin 3 → ℝ) :
    FiniteModeState FiniteModeAffineQuadraticPressureIndex
  | Sum.inl j => c j
  | Sum.inr (Sum.inl j) => A j j
  | Sum.inr (Sum.inr r) =>
      A (finiteModeOffDiagonalPair r).1 (finiteModeOffDiagonalPair r).2

/-- Affine vector field `x ↦ c + A x` on `ℝ^3`. -/
def finiteModeAffineGradientField
    (c : NSSpace) (A : Fin 3 → Fin 3 → ℝ) : NSSpace → NSSpace :=
  fun x => c + ∑ k : Fin 3,
    (∑ j : Fin 3, A k j * x j) • EuclideanSpace.single k (1 : ℝ)

set_option maxHeartbeats 800000

/-- Every affine curl-free vector field is generated by the affine-quadratic
pressure basis.  Curl-freeness is encoded by symmetry of the linear part. -/
theorem finiteModeAffineQuadraticPressureGradientSynthesis
    (c : NSSpace) (A : Fin 3 → Fin 3 → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (x : NSSpace) :
    finiteModePressureGradientSynthesis finiteModeAffineQuadraticPressureMode
        (finiteModeAffineQuadraticPressureCoefficientsAt c A) x =
      finiteModeAffineGradientField c A x := by
  ext k
  fin_cases k <;>
    simp [finiteModePressureGradientSynthesis,
      finiteModeAffineQuadraticPressureMode,
      finiteModeAffineQuadraticPressureCoefficientsAt,
      finiteModeAffineGradientField,
      finiteModeOffDiagonalPair,
      finiteModeCoordinatePressureMode_gradient,
      finiteModeDiagonalQuadraticPressureMode_gradient,
      finiteModeMixedQuadraticPressureMode_gradient,
      Fintype.sum_sum_type, hA, Fin.sum_univ_three, add_comm, add_left_comm, add_assoc,
      mul_comm]

/-- Affine curl-free vector fields lie in the finite pressure-gradient range. -/
theorem finiteModeAffineQuadraticPressureGradient_mem_range
    (c : NSSpace) (A : Fin 3 → Fin 3 → ℝ)
    (hA : ∀ i j, A i j = A j i) :
    finiteModeAffineGradientField c A ∈
      range (finiteModePressureGradientSynthesis finiteModeAffineQuadraticPressureMode) := by
  refine ⟨finiteModeAffineQuadraticPressureCoefficientsAt c A, ?_⟩
  funext x
  exact finiteModeAffineQuadraticPressureGradientSynthesis c A hA x

/-- The affine-quadratic pressure basis consists of differentiable pressure
modes. -/
theorem finiteModeAffineQuadraticPressureMode_differentiableAt
    (k : FiniteModeAffineQuadraticPressureIndex) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModeAffineQuadraticPressureMode k) x := by
  cases k with
  | inl j => exact finiteModeCoordinatePressureMode_differentiableAt j x
  | inr q =>
      cases q with
      | inl j => exact finiteModeDiagonalQuadraticPressureMode_differentiableAt j x
      | inr r =>
          fin_cases r <;>
            simp [finiteModeAffineQuadraticPressureMode, finiteModeOffDiagonalPair,
              finiteModeMixedQuadraticPressureMode_differentiableAt]

end NavierStokes
end FluidDynamics
end Mettapedia
