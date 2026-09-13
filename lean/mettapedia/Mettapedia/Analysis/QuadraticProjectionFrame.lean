import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# A fixed projection frame for products of vector magnitudes

Five points on the quadratic moment curve in three dimensions detect
every pair of nonzero vectors. Even projection moments therefore control
products of powers of their norms, with constants depending only on the
fixed frame and exponents. No direction is chosen from a spatial field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.QuadraticProjectionFrame

open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def direction (k : Fin 5) : R3 := WithLp.toLp 2 ![1, (k : ℝ), (k : ℝ) ^ 2]

theorem inner_direction (k : Fin 5) (a : R3) :
    ⟪direction k, a⟫ = a 0 + (k : ℝ) * a 1 + (k : ℝ) ^ 2 * a 2 := by
  simp [direction, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two, mul_comm]

/-- No two planes through the origin cover the five directions. -/
theorem exists_inner_mul_ne_zero (a z : R3) (ha : a ≠ 0) (hz : z ≠ 0) :
    ∃ k : Fin 5, ⟪direction k, a⟫ * ⟪direction k, z⟫ ≠ 0 := by
  by_contra hn
  have h (k : Fin 5) : ⟪direction k, a⟫ = 0 ∨ ⟪direction k, z⟫ = 0 :=
    mul_eq_zero.mp (not_not.mp (fun hk ↦ hn ⟨k, hk⟩))
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  norm_num [inner_direction] at h0 h1 h2 h3 h4
  have hext (x : R3) (h0 : x 0 = 0) (h1 : x 1 = 0) (h2 : x 2 = 0) : x = 0 := by
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have he : a = 0 ∨ z = 0 := by
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
    all_goals first
      | exact Or.inl (hext a (by linarith only [h0, h1, h2, h3, h4])
          (by linarith only [h0, h1, h2, h3, h4]) (by linarith only [h0, h1, h2, h3, h4]))
      | exact Or.inr (hext z (by linarith only [h0, h1, h2, h3, h4])
          (by linarith only [h0, h1, h2, h3, h4]) (by linarith only [h0, h1, h2, h3, h4]))
  exact he.elim ha hz

def moment (m n : ℕ) (a z : R3) : ℝ :=
  ∑ k : Fin 5, (⟪direction k, a⟫ ^ 2) ^ m * (⟪direction k, z⟫ ^ 2) ^ n

def weight (m n : ℕ) : ℝ :=
  ∑ k : Fin 5, ‖direction k‖ ^ (2 * m) * ‖direction k‖ ^ (2 * n)

theorem moment_nonneg (m n : ℕ) (a z : R3) : 0 ≤ moment m n a z := by
  unfold moment
  positivity

theorem moment_pos (m n : ℕ) (a z : R3) (ha : a ≠ 0) (hz : z ≠ 0) :
    0 < moment m n a z := by
  obtain ⟨k, hk⟩ := exists_inner_mul_ne_zero a z ha hz
  have ha' := (mul_ne_zero_iff.mp hk).1
  have hz' := (mul_ne_zero_iff.mp hk).2
  unfold moment
  exact Finset.sum_pos' (fun _ _ ↦ by positivity)
    ⟨k, Finset.mem_univ k, mul_pos (pow_pos (sq_pos_of_ne_zero ha') m)
      (pow_pos (sq_pos_of_ne_zero hz') n)⟩

theorem continuous_moment (m n : ℕ) : Continuous (fun p : R3 × R3 ↦ moment m n p.1 p.2) := by
  unfold moment
  fun_prop

theorem moment_smul (m n : ℕ) (α β : ℝ) (a z : R3) :
    moment m n (α • a) (β • z) =
      (α ^ (2 * m) * β ^ (2 * n)) * moment m n a z := by
  simp only [moment, real_inner_smul_right, mul_pow, ← pow_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem moment_le (m n : ℕ) (a z : R3) :
    moment m n a z ≤ weight m n * ‖a‖ ^ (2 * m) * ‖z‖ ^ (2 * n) := by
  have hc (e x : R3) : ⟪e, x⟫ ^ 2 ≤ ‖e‖ ^ 2 * ‖x‖ ^ 2 := by
    simpa only [sq, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le e x
  calc
    _ ≤ ∑ k : Fin 5, (‖direction k‖ ^ 2 * ‖a‖ ^ 2) ^ m *
        (‖direction k‖ ^ 2 * ‖z‖ ^ 2) ^ n :=
      Finset.sum_le_sum (fun k _ ↦ mul_le_mul
        (pow_le_pow_left₀ (sq_nonneg _) (hc _ _) m)
        (pow_le_pow_left₀ (sq_nonneg _) (hc _ _) n) (by positivity) (by positivity))
    _ = _ := by
      simp only [weight, Finset.sum_mul, mul_pow, ← pow_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem norm_direction_zero : ‖direction 0‖ = 1 := by
  have he : direction 0 = EuclideanSpace.single 0 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [direction, Matrix.cons_val_two]
  simp [he]

theorem weight_pos (m n : ℕ) : 0 < weight m n := by
  unfold weight
  apply Finset.sum_pos' (fun _ _ ↦ by positivity)
  exact ⟨0, Finset.mem_univ 0, by simp [norm_direction_zero]⟩

theorem exists_unit_lower_bound (m n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ a z : R3, ‖a‖ = 1 → ‖z‖ = 1 → c ≤ moment m n a z := by
  let K : Set (R3 × R3) := Metric.sphere 0 1 ×ˢ Metric.sphere 0 1
  have hK : IsCompact K := (isCompact_sphere (0 : R3) 1).prod (isCompact_sphere (0 : R3) 1)
  have hne : K.Nonempty := ⟨(direction 0, direction 0), by
    simp [K, norm_direction_zero]⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne (continuous_moment m n).continuousOn
  change ∀ q ∈ K, moment m n p.1 p.2 ≤ moment m n q.1 q.2 at hmin
  have hn : ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 := by simpa [K, Metric.mem_sphere, dist_zero_right] using hp
  refine ⟨moment m n p.1 p.2, moment_pos m n _ _ ?_ ?_, ?_⟩
  · intro h
    simpa [h] using hn.1
  · intro h
    simpa [h] using hn.2
  · intro a z ha hz
    exact hmin (a, z) (by simp [K, ha, hz])

/-- The same constant works for all vector pairs, including zeros. -/
theorem exists_lower_bound (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a z : R3,
      c * ‖a‖ ^ (2 * m) * ‖z‖ ^ (2 * n) ≤ moment m n a z := by
  obtain ⟨c, hc, hunit⟩ := exists_unit_lower_bound m n
  refine ⟨c, hc, fun a z ↦ ?_⟩
  by_cases ha : a = 0
  · simpa [ha, show 2 * m ≠ 0 by omega] using moment_nonneg m n a z
  by_cases hz : z = 0
  · simpa [hz, show 2 * n ≠ 0 by omega] using moment_nonneg m n a z
  let A : R3 := ‖a‖⁻¹ • a
  let Z : R3 := ‖z‖⁻¹ • z
  have hA : ‖A‖ = 1 := norm_smul_inv_norm ha
  have hZ : ‖Z‖ = 1 := norm_smul_inv_norm hz
  have haA : ‖a‖ • A = a := by
    simp [A, smul_smul, norm_ne_zero_iff.mpr ha]
  have hzZ : ‖z‖ • Z = z := by
    simp [Z, smul_smul, norm_ne_zero_iff.mpr hz]
  have h := mul_le_mul_of_nonneg_left (hunit A Z hA hZ)
    (show 0 ≤ ‖a‖ ^ (2 * m) * ‖z‖ ^ (2 * n) by positivity)
  have he := moment_smul m n ‖a‖ ‖z‖ A Z
  rw [haA, hzZ] at he
  rw [he]
  nlinarith only [h]

end Mettapedia.Analysis.QuadraticProjectionFrame
