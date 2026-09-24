import Mettapedia.Analysis.VorticityJetSource
import Mettapedia.Analysis.RegularizedProjection

/-!
# Scalar-reference cancellation in weighted projection production

The changing sixth-power weight and the symmetric curl source cancel
their common scalar-strain contribution except for a regularization term.
The entire shifted strain remains; no smallness of its rows is inferred.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.VorticityStrainProduction

open scoped RealInnerProductSpace
open VorticityJetSource WeightedCurlCancellation RegularizedProjection EuclideanCrossProduct
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def rowAction (G : Fin 3 → R3) (a : R3) : R3 :=
  WithLp.toLp 2 (fun m ↦ ⟪G m, a⟫)

def scalarShift (σ : ℝ) (G : Fin 3 → R3) (m : Fin 3) : R3 :=
  G m - σ • EuclideanSpace.single m 1

theorem rowAction_scalarShift (σ : ℝ) (G : Fin 3 → R3) (a : R3) :
    rowAction (scalarShift σ G) a = rowAction G a - σ • a := by
  ext m
  simp [rowAction, scalarShift, inner_sub_left, real_inner_smul_left, EuclideanSpace.inner_single_left]

theorem source_scalarShift (σ : ℝ) (G D : Fin 3 → R3) :
    source (scalarShift σ G) D = source G D + (2 * σ) • curlJet D := by
  ext i
  fin_cases i <;>
    simp [source, scalarShift, cross, cross_apply, curlJet,
      Fin.sum_univ_three, Matrix.cons_val_two] <;> ring

def weightedProduction (δ : ℝ) (a b : R3) (D G : Fin 3 → R3) : ℝ :=
  6 * ‖a‖ ^ 4 * ⟪a, rowAction G a⟫ * energy δ a b + ‖a‖ ^ 6 *
    (-2 * ⟪residual δ a b, rowAction G (residual δ a b)⟫ -
      4 * coefficient δ a b * ⟪residual δ a b, rowAction G a⟫ +
      2 * ⟪residual δ a b, source G D⟫)

/-- Curl compatibility is used in the scalar source term. The identity
does not assume that the shifted strain vanishes or is small. -/
theorem weightedProduction_eq_shift (δ : ℝ) (hδ : 0 < δ) (a b : R3)
    (D G : Fin 3 → R3) (hb : b = curlJet D) (σ : ℝ) :
    weightedProduction δ a b D G = weightedProduction δ a b D (scalarShift σ G) -
      2 * σ * δ * coefficient δ a b ^ 2 * ‖a‖ ^ 6 := by
  have hi : ⟪residual δ a b, a⟫ = δ * coefficient δ a b :=
    (real_inner_comm _ _).trans (inner_residual δ hδ a b)
  simp only [weightedProduction, rowAction_scalarShift, source_scalarShift, ← hb,
    inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    inner_residual_eq_energy δ hδ, hi]
  unfold energy
  ring

def rankOneRows (c : ℝ) (n : R3) (m : Fin 3) : R3 := (c * n m) • n

theorem rowAction_rankOneRows (c : ℝ) (n a : R3) :
    rowAction (rankOneRows c n) a = (c * ⟪n, a⟫) • n := by
  ext m
  simp only [rowAction, rankOneRows, real_inner_smul_left, PiLp.smul_apply, smul_eq_mul]
  change c * n m * ⟪n, a⟫ = (c * ⟪n, a⟫) * n m
  ring

/-- A rank-one normal strain only sees the vorticity derivative in that
normal direction. Its size is not bounded by this identity. -/
theorem source_rankOneRows (c : ℝ) (n : R3) (D : Fin 3 → R3) :
    source (rankOneRows c n) D = -(2 * c) • cross n (∑ m : Fin 3, n m • D m) := by
  simp only [source, rankOneRows, Fin.sum_univ_three, cross_add_right,
    cross_smul_left, cross_smul_right]
  module

/-- The full production for a normal rank-one strain. The normal
components and the normal derivative remain separate signed terms. -/
theorem weightedProduction_rankOneRows (δ c : ℝ) (a b n : R3) (D : Fin 3 → R3) :
    weightedProduction δ a b D (rankOneRows c n) =
      6 * c * ‖a‖ ^ 4 * ⟪a, n⟫ ^ 2 * energy δ a b + ‖a‖ ^ 6 *
        (-2 * c * ⟪residual δ a b, n⟫ ^ 2 -
          4 * c * coefficient δ a b * ⟪residual δ a b, n⟫ * ⟪a, n⟫ -
          4 * c * ⟪residual δ a b, cross n (∑ m : Fin 3, n m • D m)⟫) := by
  simp only [weightedProduction, rowAction_rankOneRows, source_rankOneRows, real_inner_smul_right,
    real_inner_comm a n, real_inner_comm (residual δ a b) n]
  ring

end Mettapedia.Analysis.VorticityStrainProduction
