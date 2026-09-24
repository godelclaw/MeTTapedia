import Mettapedia.Analysis.EuclideanCrossProduct
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltSymbol

/-!
# Coherent pressure pairs with nearly cancelling input frequencies

The real Biot--Savart pair kernel is treated before any convolution
estimate. The cross-product numerator retains its vanishing at cancelling
frequencies. No lower bound on the output frequency is imposed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair

open scoped RealInnerProductSpace
open Mettapedia.Analysis.EuclideanCrossProduct
open PancakeAnisotropyDepletion PressureTiltSymbol

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The real bilinear trace kernel after curl inversion. The physical
complex Fourier phases are separate from this real kernel. -/
def tracePair (k p w v : E3) : ℝ :=
  ⟪p, cross k w⟫ * ⟪k, cross p v⟫ / (‖k‖ ^ 2 * ‖p‖ ^ 2)

def tiltPair (e k p w v : E3) : E3 := tracePair k p w v • tiltSymbol e (k + p)

theorem tracePair_swap (k p w v : E3) : tracePair p k v w = tracePair k p w v := by
  unfold tracePair
  ring

theorem tiltPair_swap (e k p w v : E3) : tiltPair e p k v w = tiltPair e k p w v := by
  rw [tiltPair, tracePair_swap, add_comm]
  rfl

theorem tracePair_coherent (e k p : E3) :
    tracePair k p e e = -⟪e, cross k p⟫ ^ 2 / (‖k‖ ^ 2 * ‖p‖ ^ 2) := by
  have h1 : ⟪p, cross k e⟫ = -⟪e, cross k p⟫ := by
    rw [inner_cross_cycle, inner_cross_cycle, cross_swap, inner_neg_right]
  have h2 : ⟪k, cross p e⟫ = ⟪e, cross k p⟫ := by
    rw [inner_cross_cycle, inner_cross_cycle]
  rw [tracePair, h1, h2]
  ring

theorem norm_tiltSymbol_mul_norm_le (e q : E3) (he : ‖e‖ = 1) :
    ‖tiltSymbol e q‖ * ‖q‖ ≤ |⟪q, e⟫| := by
  by_cases hq : q = 0
  · simp [hq]
  · have hqn := norm_pos_iff.mpr hq
    rw [tiltSymbol, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (sq_nonneg ‖q‖)]
    calc
      _ ≤ (|⟪q, e⟫| / ‖q‖ ^ 2) * ‖q‖ * ‖q‖ := by
        gcongr
        exact norm_lineRemainder_le e q he
      _ = _ := by field_simp

theorem norm_tiltPair_coherent (e k p : E3) :
    ‖tiltPair e k p e e‖ =
      ‖tiltSymbol e (k + p)‖ * ⟪e, cross k p⟫ ^ 2 / (‖k‖ ^ 2 * ‖p‖ ^ 2) := by
  rw [tiltPair, norm_smul, Real.norm_eq_abs, tracePair_coherent, abs_div, abs_neg,
    abs_of_nonneg (sq_nonneg _), abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  ring

theorem abs_triple_le (e k p : E3) (he : ‖e‖ = 1) : |⟪e, cross k p⟫| ≤ ‖k‖ * ‖p‖ := by
  have h := abs_real_inner_le_norm e (cross k p)
  rw [he, one_mul] at h
  exact h.trans (norm_cross_le k p)

theorem norm_tiltPair_coherent_le_of_norm_le (e k p : E3) (he : ‖e‖ = 1)
    (hk : k ≠ 0) (hp : p ≠ 0) (hkp : ‖k‖ ≤ ‖p‖) :
    ‖tiltPair e k p e e‖ ≤ |⟪k, e⟫| / ‖k‖ + |⟪p, e⟫| / ‖p‖ := by
  have hkn := norm_pos_iff.mpr hk
  have hpn := norm_pos_iff.mpr hp
  have h1 := abs_triple_le e k p he
  have h2 := abs_triple_le e k (k + p) he
  rw [cross_add_right, cross_self, zero_add] at h2
  have hprod := mul_le_mul h1 h2 (abs_nonneg _) (by positivity : 0 ≤ ‖k‖ * ‖p‖)
  have hT : ⟪e, cross k p⟫ ^ 2 ≤ ‖k‖ ^ 2 * ‖p‖ * ‖k + p‖ := by
    nlinarith only [hprod, sq_abs ⟪e, cross k p⟫]
  have ht := norm_tiltSymbol_mul_norm_le e (k + p) he
  have hraw : ‖tiltSymbol e (k + p)‖ * ⟪e, cross k p⟫ ^ 2 ≤
      ‖k‖ ^ 2 * ‖p‖ * |⟪k + p, e⟫| := by
    have h3 := mul_le_mul_of_nonneg_left hT (norm_nonneg (tiltSymbol e (k + p)))
    have h4 := mul_le_mul_of_nonneg_left ht (show 0 ≤ ‖k‖ ^ 2 * ‖p‖ by positivity)
    nlinarith only [h3, h4]
  rw [norm_tiltPair_coherent]
  calc
    _ ≤ (‖k‖ ^ 2 * ‖p‖ * |⟪k + p, e⟫|) / (‖k‖ ^ 2 * ‖p‖ ^ 2) :=
      div_le_div_of_nonneg_right hraw (by positivity)
    _ = |⟪k + p, e⟫| / ‖p‖ := by field_simp
    _ ≤ (|⟪k, e⟫| + |⟪p, e⟫|) / ‖p‖ := by
      apply div_le_div_of_nonneg_right _ hpn.le
      rw [inner_add_left]
      exact abs_add_le _ _
    _ = |⟪k, e⟫| / ‖p‖ + |⟪p, e⟫| / ‖p‖ := add_div _ _ _
    _ ≤ |⟪k, e⟫| / ‖k‖ + |⟪p, e⟫| / ‖p‖ :=
      add_le_add (div_le_div_of_nonneg_left (abs_nonneg ⟪k, e⟫) hkn hkp) le_rfl

theorem norm_tiltPair_coherent_le (e k p : E3) (he : ‖e‖ = 1) :
    ‖tiltPair e k p e e‖ ≤ |⟪k, e⟫| / ‖k‖ + |⟪p, e⟫| / ‖p‖ := by
  by_cases hk : k = 0
  · subst k
    simp only [tiltPair, tracePair, zero_cross, inner_zero_right, mul_zero, zero_div,
      zero_smul, norm_zero, inner_zero_left, zero_add]
    positivity
  by_cases hp : p = 0
  · subst p
    simp only [tiltPair, tracePair, zero_cross, inner_zero_right, mul_zero, zero_div,
      zero_smul, norm_zero, inner_zero_left, add_zero]
    positivity
  rcases le_total ‖k‖ ‖p‖ with h | h
  · exact norm_tiltPair_coherent_le_of_norm_le e k p he hk hp h
  · simpa only [tiltPair_swap, add_comm] using norm_tiltPair_coherent_le_of_norm_le e p k he hp hk h

end Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair
