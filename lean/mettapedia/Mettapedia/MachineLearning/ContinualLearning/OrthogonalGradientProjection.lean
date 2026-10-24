import Mettapedia.MachineLearning.ContinualLearning.GradientProjectionMemory
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Multi-direction orthogonal gradient projection

Farajtabar et al., *Orthogonal Gradient Descent for Continual Learning*
(2020), Algorithm 1, Equation (9), and Lemma 3.1, subtract the projection of a
new-task gradient onto an orthogonal basis of stored model gradients.  The
remaining direction is orthogonal to every stored basis vector and its
negative remains a descent direction for the current loss.

This file recovers the multi-direction theorem in finite real coordinates.
With orthonormal stored columns, the residual update is annihilated by the
stored basis, decomposes the current gradient orthogonally, and satisfies the
exact identity

`⟪-residual, gradient⟫ = -‖residual‖²`.

The result is stronger and more informative than a weak descent inequality.
It also exposes two essential boundaries: a full stored basis leaves no
plasticity, and a nonorthonormal stored basis can turn the nominal
"projected" negative gradient into a strict ascent direction.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace OrthogonalGradientProjection

open GradientProjectionMemory

noncomputable section

variable {Coordinate Basis : Type*}
  [Fintype Coordinate] [Fintype Basis]
  [DecidableEq Coordinate] [DecidableEq Basis]

/-- Algorithm 1 / Equation (9): remove all components represented by the
stored gradient basis. -/
def projectedGradient
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Coordinate → ℝ) : Coordinate → ℝ :=
  (residualProjector memory).mulVec gradient

omit [DecidableEq Basis] in
/-- The residual-projector formula is the original gradient minus its stored
subspace component. -/
theorem projectedGradient_eq_sub_projector
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Coordinate → ℝ) :
    projectedGradient memory gradient =
      gradient - (projector memory).mulVec gradient := by
  simp [projectedGradient, residualProjector, Matrix.sub_mulVec]

/-- Orthonormal stored columns make the projected gradient exactly
orthogonal to every stored direction. -/
theorem transpose_mulVec_projectedGradient_eq_zero
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    memory.transpose.mulVec (projectedGradient memory gradient) = 0 := by
  simpa [projectedGradient, residualProjector, convolutionalUpdate,
    Matrix.mulVec_mulVec] using congrArg (fun matrix => matrix.mulVec gradient)
      (convolutionalUpdate_annihilates_basis memory orthonormal 1)

/-- The projected gradient is orthogonal to the component removed by the
stored projector. -/
theorem projectedGradient_dot_removed_eq_zero
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    projectedGradient memory gradient ⬝ᵥ
        (projector memory).mulVec gradient = 0 := by
  rw [projector, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  have orthogonal := transpose_mulVec_projectedGradient_eq_zero memory orthonormal gradient
  simp only [← Matrix.vecMul_transpose memory.transpose,
    Matrix.transpose_transpose] at orthogonal
  rw [orthogonal]
  simp

/-- Exact Pythagorean identity behind OGD's current-task descent claim. -/
theorem projectedGradient_dot_gradient_eq_self
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    projectedGradient memory gradient ⬝ᵥ gradient =
      projectedGradient memory gradient ⬝ᵥ
        projectedGradient memory gradient := by
  have orthogonal := projectedGradient_dot_removed_eq_zero memory orthonormal gradient
  conv_rhs => arg 2; rw [projectedGradient_eq_sub_projector]
  rw [dotProduct_sub, orthogonal, sub_zero]

omit [Fintype Basis] [DecidableEq Coordinate] [DecidableEq Basis] in
/-- Squared Euclidean length is nonnegative in finite real coordinates. -/
theorem dotProduct_self_nonnegative_local
    (vector : Coordinate → ℝ) :
    0 ≤ vector ⬝ᵥ vector := by
  exact Finset.sum_nonneg (fun coordinate _ => mul_self_nonneg (vector coordinate))

/-- Source Lemma 3.1, sharpened to equality: the negative projected gradient
has directional derivative exactly minus its squared Euclidean length. -/
theorem neg_projectedGradient_dot_gradient
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    (-projectedGradient memory gradient) ⬝ᵥ gradient =
      -(projectedGradient memory gradient ⬝ᵥ
          projectedGradient memory gradient) := by
  rw [neg_dotProduct,
    projectedGradient_dot_gradient_eq_self
      memory orthonormal gradient]

/-- The OGD direction is always a weak descent direction. -/
theorem neg_projectedGradient_dot_gradient_nonpos
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    (-projectedGradient memory gradient) ⬝ᵥ gradient ≤ 0 := by
  rw [neg_projectedGradient_dot_gradient memory orthonormal]
  exact neg_nonpos.mpr (dotProduct_self_nonnegative_local _)

/-- It is a strict descent direction exactly when some plastic component
survives the projection. -/
theorem neg_projectedGradient_dot_gradient_neg
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ)
    (nonzero : projectedGradient memory gradient ≠ 0) :
    (-projectedGradient memory gradient) ⬝ᵥ gradient < 0 := by
  rw [neg_projectedGradient_dot_gradient memory orthonormal]
  exact neg_lt_zero.mpr (lt_of_le_of_ne (dotProduct_self_nonnegative_local _)
    (Ne.symm (mt dotProduct_self_eq_zero.mp nonzero)))

omit [DecidableEq Basis] in
/-- Zero memory recovers the ordinary current-task gradient. -/
theorem zeroMemory_projectedGradient
    (gradient : Coordinate → ℝ) :
    projectedGradient (0 : Matrix Coordinate Basis ℝ) gradient =
      gradient := by
  simp [projectedGradient, residualProjector, projector]

/-- A complete coordinate basis removes every gradient and therefore every
strictly improving first-order direction. -/
theorem identityMemory_erases_gradient
    (gradient : Coordinate → ℝ) :
    projectedGradient (1 : Matrix Coordinate Coordinate ℝ) gradient =
      0 := by
  simp [projectedGradient, residualProjector, projector]

/-! ## Executable positive and negative fixtures -/

set_option backward.isDefEq.respectTransparency false in
/-- Storing the first coordinate preserves it and leaves a second-coordinate
gradient live, with exact descent margin four. -/
theorem firstAxisMemory_projects_to_second :
    let memory : Matrix (Fin 2) Unit ℝ :=
      fun coordinate _ => if coordinate = 0 then 1 else 0
    let gradient : Fin 2 → ℝ :=
      fun coordinate => if coordinate = 0 then 1 else 2
    HasOrthonormalColumns memory ∧
      projectedGradient memory gradient =
        (fun coordinate => if coordinate = 0 then 0 else 2) ∧
      (-projectedGradient memory gradient) ⬝ᵥ gradient = -4 := by
  norm_num [HasOrthonormalColumns, projectedGradient, residualProjector, projector,
    ← Matrix.ext_iff, funext_iff, Matrix.mulVec, Matrix.mul_apply, Matrix.one_apply,
    dotProduct, Fin.sum_univ_two, Fin.forall_fin_succ]

set_option backward.isDefEq.respectTransparency false in
/-- Orthonormality is load-bearing.  In one dimension a stored vector of
length two produces the operator `I-4I=-3I`; following the negative nominal
projected gradient then has positive directional derivative and is strict
ascent. -/
theorem nonorthonormal_scalar_memory_reverses_descent :
    let memory : Matrix Unit Unit ℝ := fun _ _ => 2
    let gradient : Unit → ℝ := fun _ => 1
    ¬ HasOrthonormalColumns memory ∧
      projectedGradient memory gradient = (fun _ => -3) ∧
      (-projectedGradient memory gradient) ⬝ᵥ gradient = 3 := by
  norm_num [HasOrthonormalColumns, projectedGradient, residualProjector, projector,
    ← Matrix.ext_iff, funext_iff, Matrix.mulVec, Matrix.mul_apply, dotProduct]


end

end OrthogonalGradientProjection

end Mettapedia.MachineLearning.ContinualLearning
