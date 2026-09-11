import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Coordinates of Euclidean bilinear operators

Elementary bilinear operators have norm at most one. Their finite linear
combination reconstructs any continuous bilinear operator from its values
on coordinate vectors, and the sum of absolute entries bounds its norm.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanBilinearCoordinates

variable {𝕜 I J K : Type*} [RCLike 𝕜] [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

local notation "U" => EuclideanSpace 𝕜 I
local notation "V" => EuclideanSpace 𝕜 J
local notation "W" => EuclideanSpace 𝕜 K
local notation "Op" => U →L[𝕜] V →L[𝕜] W

local instance : NormedAddCommGroup (V →L[𝕜] W) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace 𝕜 (V →L[𝕜] W) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace 𝕜 Op := ContinuousLinearMap.toNormedSpace

def elementaryLinear (i : K) (j : I) (l : J) : U →ₗ[𝕜] V →ₗ[𝕜] W :=
  LinearMap.mk₂ 𝕜 (fun u v ↦ (u j * v l) • EuclideanSpace.single i 1)
    (fun u z v ↦ by simp [add_mul, add_smul])
    (fun a u v ↦ by simp [mul_smul, mul_assoc])
    (fun u v z ↦ by simp [mul_add, add_smul])
    (fun a u v ↦ by simp [mul_smul, mul_left_comm])

omit [DecidableEq I] [DecidableEq J] in
theorem norm_elementaryLinear_le (i : K) (j : I) (l : J) (u : U) (v : V) :
    ‖elementaryLinear i j l u v‖ ≤ 1 * ‖u‖ * ‖v‖ := by
  simp only [elementaryLinear, LinearMap.mk₂_apply, norm_smul, norm_mul,
    PiLp.norm_single, norm_one, mul_one, one_mul]
  exact mul_le_mul (PiLp.norm_apply_le u j) (PiLp.norm_apply_le v l) (norm_nonneg _) (norm_nonneg _)

def elementary (i : K) (j : I) (l : J) : Op :=
  (elementaryLinear (𝕜 := 𝕜) i j l).mkContinuous₂ 1 (norm_elementaryLinear_le i j l)

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem elementary_apply (i : K) (j : I) (l : J) (u : U) (v : V) :
    elementary i j l u v = (u j * v l) • EuclideanSpace.single i 1 := rfl

omit [DecidableEq I] [DecidableEq J] in
theorem norm_elementary_le (i : K) (j : I) (l : J) : ‖elementary (𝕜 := 𝕜) i j l‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

theorem sum_coordinates (u : U) : ∑ j, u j • EuclideanSpace.single j (1 : 𝕜) = u := by
  ext j
  simp [Pi.single_apply]

omit [DecidableEq K] in
theorem ext_basis {B C : Op}
    (h : ∀ j l, B (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) =
      C (EuclideanSpace.single j 1) (EuclideanSpace.single l 1)) : B = C := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  conv_lhs => arg 1; arg 2; rw [← sum_coordinates u]
  conv_rhs => arg 1; arg 2; rw [← sum_coordinates u]
  simp only [map_sum, map_smul, sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← sum_coordinates v, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul, map_smul, h]

def entry (B : Op) (i : K) (j : I) (l : J) : 𝕜 :=
  B (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i

def reconstruct (c : K → I → J → 𝕜) : Op :=
  ∑ i, ∑ j, ∑ l, c i j l • elementary i j l

theorem reconstruct_apply_basis (c : K → I → J → 𝕜) (j : I) (l : J) :
    reconstruct c (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) =
      ∑ i, c i j l • EuclideanSpace.single i 1 := by
  simp [reconstruct, elementary_apply]

theorem reconstruct_entry (B : Op) : reconstruct (entry B) = B := by
  apply ext_basis
  intro j l
  rw [reconstruct_apply_basis]
  exact sum_coordinates _

omit [DecidableEq I] [DecidableEq J] in
theorem norm_reconstruct_le (c : K → I → J → 𝕜) :
    ‖reconstruct c‖ ≤ ∑ i, ∑ j, ∑ l, ‖c i j l‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_elementary_le i j l)

end Mettapedia.Analysis.EuclideanBilinearCoordinates
