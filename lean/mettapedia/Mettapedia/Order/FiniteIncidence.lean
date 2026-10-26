import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite incidence transforms

Mass is indexed by individual poset elements; the zeta transform observes its
sum below each query. All those observations together determine the mass,
although the inverse of a monotone function need not be nonnegative.

Incidence kernels act on row vectors. Applying `A` and then `B` therefore
corresponds to `A * B`, with the order of the two actions explicit.
-/

namespace Mettapedia.Order.FiniteIncidence

open Finset Matrix
open scoped BigOperators Matrix

section LowerSum
variable {P A : Type*} [Fintype P] [LE P] [DecidableLE P] [AddCommMonoid A]

def lowerSet (y : P) : Finset P := univ.filter (· ≤ y)

def lowerSum (f : P → A) (y : P) : A := ∑ x ∈ lowerSet y, f x

@[simp] theorem mem_lowerSet (x y : P) : x ∈ lowerSet y ↔ x ≤ y := by simp [lowerSet]

theorem lowerSum_add (f g : P → A) (y : P) :
    lowerSum (f + g) y = lowerSum f y + lowerSum g y := by
  simp [lowerSum, sum_add_distrib]
end LowerSum

section Kernels
variable {P R : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
local instance : DecidableLT P := fun a b =>
  decidable_of_iff (a ≤ b ∧ a ≠ b) lt_iff_le_and_ne.symm
local instance : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder

def kernelMatrix [Zero R] (K : IncidenceAlgebra R P) : Matrix P P R := fun x y => K x y

variable [CommRing R]

theorem kernelMatrix_mul (A B : IncidenceAlgebra R P) :
    kernelMatrix (A * B) = kernelMatrix A * kernelMatrix B := by
  ext x y
  simp only [kernelMatrix, Matrix.mul_apply, IncidenceAlgebra.mul_apply]
  apply sum_subset (subset_univ _)
  intro z _ outside
  have not_both : ¬ (x ≤ z ∧ z ≤ y) := by simpa using outside
  rcases not_and_or.mp not_both with first | second
  · rw [IncidenceAlgebra.apply_eq_zero_of_not_le first, zero_mul]
  · rw [IncidenceAlgebra.apply_eq_zero_of_not_le second, mul_zero]

def kernelMatrixHom : IncidenceAlgebra R P →+* Matrix P P R where
  toFun := kernelMatrix
  map_one' := by ext; simp [kernelMatrix, Matrix.one_apply]
  map_mul' := kernelMatrix_mul
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fintype P] [DecidableEq P] [DecidableLE P] in
theorem kernelMatrix_injective : Function.Injective (kernelMatrix : IncidenceAlgebra R P → Matrix P P R) := by
  intro A B same
  apply IncidenceAlgebra.ext
  intro x y _
  exact congrFun (congrFun same x) y

theorem kernel_composition (A B : IncidenceAlgebra R P) (f : P → R) :
    (f ᵥ* kernelMatrix A) ᵥ* kernelMatrix B = f ᵥ* kernelMatrix (A * B) := by
  rw [kernelMatrix_mul, Matrix.vecMul_vecMul]

omit [DecidableEq P] in
/-- The explicit finite sum is independent of the matrix representation. -/
theorem row_apply (K : IncidenceAlgebra R P) (f : P → R) (y : P) :
    (f ᵥ* kernelMatrix K) y = lowerSum (fun x => f x * K x y) y := by
  unfold Matrix.vecMul dotProduct lowerSum
  symm
  apply sum_subset (filter_subset _ _)
  intro x _ outside
  have not_le : ¬x ≤ y := by simpa [lowerSet] using outside
  simp [IncidenceAlgebra.apply_eq_zero_of_not_le not_le]

omit [DecidableEq P] in
theorem zeta_row (f : P → R) :
    f ᵥ* kernelMatrix (IncidenceAlgebra.zeta R) = lowerSum f := by
  funext y
  rw [row_apply]
  unfold lowerSum
  apply sum_congr rfl
  intro x hx
  simp [IncidenceAlgebra.zeta_apply, (mem_lowerSet x y).mp hx]

/-- All lower-set observations form an exact change of linear coordinates. -/
def zetaEquiv : (P → R) ≃ₗ[R] (P → R) where
  toLinearMap := (kernelMatrix (IncidenceAlgebra.zeta R)).vecMulLinear
  invFun f := f ᵥ* kernelMatrix (IncidenceAlgebra.mu R)
  left_inv f := by
    change (f ᵥ* kernelMatrix (IncidenceAlgebra.zeta R)) ᵥ*
      kernelMatrix (IncidenceAlgebra.mu R) = f
    rw [Matrix.vecMul_vecMul, ← kernelMatrix_mul, IncidenceAlgebra.zeta_mul_mu]
    rw [show kernelMatrix (1 : IncidenceAlgebra R P) = 1 from kernelMatrixHom.map_one, Matrix.vecMul_one]
  right_inv f := by
    change (f ᵥ* kernelMatrix (IncidenceAlgebra.mu R)) ᵥ*
      kernelMatrix (IncidenceAlgebra.zeta R) = f
    rw [Matrix.vecMul_vecMul, ← kernelMatrix_mul, IncidenceAlgebra.mu_mul_zeta]
    rw [show kernelMatrix (1 : IncidenceAlgebra R P) = 1 from kernelMatrixHom.map_one, Matrix.vecMul_one]

noncomputable def inverse (g : P → R) : P → R := (zetaEquiv (P := P) (R := R)).symm g

@[simp] theorem zetaEquiv_apply (f : P → R) : zetaEquiv f = lowerSum f := zeta_row f

@[simp] theorem inverse_lowerSum (f : P → R) : inverse (lowerSum f) = f :=
  by simpa only [inverse, zetaEquiv_apply] using (zetaEquiv (P := P) (R := R)).symm_apply_apply f

@[simp] theorem lowerSum_inverse (g : P → R) : lowerSum (inverse g) = g :=
  by simpa only [inverse, zetaEquiv_apply] using (zetaEquiv (P := P) (R := R)).apply_symm_apply g

theorem inverse_apply (g : P → R) (y : P) :
    inverse g y = lowerSum (fun x => IncidenceAlgebra.mu R x y * g x) y := by
  change (g ᵥ* kernelMatrix (IncidenceAlgebra.mu R)) y = _
  rw [row_apply]
  simp_rw [mul_comm]

theorem lowerSum_injective : Function.Injective (lowerSum : (P → R) → P → R) :=
  fun _ _ equal => (zetaEquiv (P := P) (R := R)).injective
    (by simpa only [zetaEquiv_apply] using equal)
end Kernels

end Mettapedia.Order.FiniteIncidence
