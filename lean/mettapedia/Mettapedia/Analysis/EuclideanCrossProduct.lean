import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Cross-product identities in three-dimensional Euclidean space -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanCrossProduct

open scoped Matrix RealInnerProductSpace
open WithLp

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def cross (u v : E3) : E3 := toLp 2 (ofLp u ⨯₃ ofLp v)

@[simp] theorem cross_self (u : E3) : cross u u = 0 := by
  simp [cross]

@[simp] theorem cross_zero (u : E3) : cross u 0 = 0 := by
  simp [cross]

@[simp] theorem zero_cross (u : E3) : cross 0 u = 0 := by
  simp [cross]

theorem cross_add_left (u v w : E3) : cross (u + v) w = cross u w + cross v w := by
  simp [cross]

theorem cross_add_right (u v w : E3) : cross u (v + w) = cross u v + cross u w := by
  simp [cross]

theorem cross_smul_left (r : ℝ) (u v : E3) : cross (r • u) v = r • cross u v := by
  simp [cross]

theorem cross_smul_right (r : ℝ) (u v : E3) : cross u (r • v) = r • cross u v := by
  simp [cross]

theorem cross_swap (u v : E3) : cross v u = -cross u v := by
  unfold cross
  rw [← cross_anticomm]
  rfl

theorem inner_self_cross (u v : E3) : ⟪u, cross u v⟫ = 0 := by
  simpa only [cross, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toLp, star_trivial,
    dotProduct_comm] using dot_self_cross (ofLp u) (ofLp v)

theorem inner_cross_self (u v : E3) : ⟪v, cross u v⟫ = 0 := by
  simpa only [cross, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toLp, star_trivial,
    dotProduct_comm] using dot_cross_self (ofLp u) (ofLp v)

theorem inner_cross_cycle (u v w : E3) : ⟪u, cross v w⟫ = ⟪v, cross w u⟫ := by
  simpa only [cross, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toLp, star_trivial,
    dotProduct_comm] using triple_product_permutation (ofLp u) (ofLp v) (ofLp w)

theorem norm_cross_sq (u v : E3) : ‖cross u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
  have hn (a : E3) : ⟪a, a⟫ = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
  rw [← hn (cross u v), ← hn u, ← hn v]
  simp only [cross, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, cross_dot_cross]
  rw [dotProduct_comm (ofLp u) (ofLp v)]
  ring

theorem norm_cross_le (u v : E3) : ‖cross u v‖ ≤ ‖u‖ * ‖v‖ := by
  have h := norm_cross_sq u v
  nlinarith only [h, sq_nonneg ⟪u, v⟫, norm_nonneg (cross u v),
    mul_nonneg (norm_nonneg u) (norm_nonneg v)]

end Mettapedia.Analysis.EuclideanCrossProduct
