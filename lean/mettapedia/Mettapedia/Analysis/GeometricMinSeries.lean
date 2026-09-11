import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A geometric series capped by a fixed cost

Summing the smaller of a geometric bound and a fixed bound incurs a
logarithmic, rather than an inverse-power, loss in their ratio. An explicit
finite-cutoff estimate precedes the optimized bound. Zero fixed cost is
included separately, so summability never relies on a formal zero value
of a divergent `tsum`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.GeometricMinSeries

theorem summable_min {A D q : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hq : 0 ≤ q) (hq1 : q < 1) : Summable (fun m : ℕ ↦ min (A * q ^ m) D) :=
  Summable.of_nonneg_of_le (fun m ↦ le_min (mul_nonneg hA (pow_nonneg hq m)) hD)
    (fun _ ↦ min_le_left _ _) ((summable_geometric_of_lt_one hq hq1).mul_left A)

theorem tsum_min_le_cutoff {A D q : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hq : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    (∑' m : ℕ, min (A * q ^ m) D) ≤ (M : ℝ) * D + A * q ^ M / (1 - q) := by
  have hs := summable_min hA hD hq hq1
  have htail : Summable (fun m : ℕ ↦ A * q ^ (m + M)) := by
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using
      (summable_geometric_of_lt_one hq hq1).mul_left (A * q ^ M)
  rw [← hs.sum_add_tsum_nat_add M]
  apply add_le_add
  · simpa using Finset.sum_le_sum (s := Finset.range M)
      (fun m (_ : m ∈ Finset.range M) ↦ min_le_right (A * q ^ m) D)
  · calc
      _ ≤ ∑' m : ℕ, A * q ^ (m + M) :=
        (hs.comp_injective (add_left_injective M)).tsum_le_tsum (fun _ ↦ min_le_left _ _) htail
      _ = _ := by
        simp only [pow_add, ← mul_assoc]
        rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hq hq1]
        ring

theorem exists_logarithmic_cutoff {A D q : ℝ} (hA : 0 ≤ A) (hD : 0 < D)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃ M : ℕ, (M : ℝ) ≤ Real.log (1 + A / D) / (-Real.log q) + 1 ∧ A * q ^ M ≤ D := by
  let L := Real.log (1 + A / D) / (-Real.log q)
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  have hsum : 0 < 1 + A / D := by positivity
  have hL : 0 ≤ L := div_nonneg
    (Real.log_nonneg (le_add_of_nonneg_right (div_nonneg hA hD.le))) (neg_nonneg.mpr hlog.le)
  refine ⟨⌈L⌉₊, (Nat.ceil_lt_add_one hL).le, ?_⟩
  have hp : q ^ (⌈L⌉₊ : ℕ) ≤ (1 + A / D)⁻¹ := by
    calc
      _ = q ^ (⌈L⌉₊ : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ q ^ L := Real.rpow_le_rpow_of_exponent_ge hq hq1.le (Nat.le_ceil L)
      _ = (1 + A / D)⁻¹ := by
        rw [Real.rpow_def_of_pos hq]
        have he : Real.log q * L = -Real.log (1 + A / D) := by
          dsimp [L]
          field_simp [hlog.ne]
        rw [he, Real.exp_neg, Real.exp_log hsum]
  calc
    A * q ^ (⌈L⌉₊ : ℕ) ≤ A * (1 + A / D)⁻¹ := mul_le_mul_of_nonneg_left hp hA
    _ ≤ D := by
      rw [← div_eq_mul_inv, div_le_iff₀ hsum]
      field_simp
      nlinarith

/-- The logarithmic loss is explicit for every geometric ratio strictly between zero and one. -/
theorem tsum_min_le_logarithmic {A D q : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hq : 0 < q) (hq1 : q < 1) :
    (∑' m : ℕ, min (A * q ^ m) D) ≤
      D * (1 + (1 - q)⁻¹ + Real.log (1 + A / D) / (-Real.log q)) := by
  by_cases hD0 : D = 0
  · subst D
    simp only [min_eq_right (mul_nonneg hA (pow_nonneg hq.le _)), tsum_zero, zero_mul]
    exact le_rfl
  · obtain ⟨M, hM, htail⟩ := exists_logarithmic_cutoff hA (lt_of_le_of_ne hD (Ne.symm hD0)) hq hq1
    calc
      _ ≤ (M : ℝ) * D + A * q ^ M / (1 - q) := tsum_min_le_cutoff hA hD hq.le hq1 M
      _ ≤ (Real.log (1 + A / D) / (-Real.log q) + 1) * D + D / (1 - q) :=
        add_le_add (mul_le_mul_of_nonneg_right hM hD)
          (div_le_div_of_nonneg_right htail (sub_nonneg.mpr hq1.le))
      _ = _ := by ring

theorem tsum_min_half_pow_le {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) :
    (∑' m : ℕ, min (A * (1 / 2 : ℝ) ^ m) D) ≤
      D * (3 + Real.log (1 + A / D) / Real.log 2) := by
  have h := tsum_min_le_logarithmic hA hD
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hlog : -Real.log (1 / 2 : ℝ) = Real.log 2 := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [hlog] at h
  norm_num at h
  exact h

/-- A nonnegative sequence below a scaled capped geometric sequence is summable,
with the same explicit logarithmic cost. -/
theorem tsum_le_logarithmic_of_nonneg_of_le {a : ℕ → ℝ} {C A D : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (ha : ∀ m, 0 ≤ a m)
    (hle : ∀ m, a m ≤ C * min (A * (1 / 2 : ℝ) ^ m) D) :
    Summable a ∧ (∑' m, a m) ≤ C * D * (3 + Real.log (1 + A / D) / Real.log 2) := by
  have hs := (summable_min hA hD (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left C
  have hsa := Summable.of_nonneg_of_le ha hle hs
  refine ⟨hsa, ?_⟩
  calc
    _ ≤ ∑' m : ℕ, C * min (A * (1 / 2 : ℝ) ^ m) D := hsa.tsum_le_tsum hle hs
    _ = C * ∑' m : ℕ, min (A * (1 / 2 : ℝ) ^ m) D := tsum_mul_left
    _ ≤ C * (D * (3 + Real.log (1 + A / D) / Real.log 2)) :=
      mul_le_mul_of_nonneg_left (tsum_min_half_pow_le hA hD) hC
    _ = _ := by ring

/-- A second geometric input index can be summed without losing the logarithmic
gain from the capped output index. Both summability claims are included. -/
theorem iterated_tsum_le_logarithmic_of_nonneg_of_le {a : ℕ → ℕ → ℝ} {C A D : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (ha : ∀ j m, 0 ≤ a j m)
    (hle : ∀ j m, a j m ≤ C * (1 / 2 : ℝ) ^ j * min (A * (1 / 2 : ℝ) ^ m) D) :
    (∀ j, Summable (a j)) ∧ Summable (fun j ↦ ∑' m, a j m) ∧
      (∑' j, ∑' m, a j m) ≤ 2 * C * D * (3 + Real.log (1 + A / D) / Real.log 2) := by
  have hi (j : ℕ) := tsum_le_logarithmic_of_nonneg_of_le
    (mul_nonneg hC (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j)) hA hD (ha j) (hle j)
  let B := C * D * (3 + Real.log (1 + A / D) / Real.log 2)
  have hs := hasSum_geometric_two.mul_left B
  have hj (j : ℕ) : (∑' m, a j m) ≤ B * (1 / 2 : ℝ) ^ j :=
    (hi j).2.trans_eq (by dsimp [B]; ring)
  have ho := Summable.of_nonneg_of_le (fun j ↦ tsum_nonneg (ha j)) hj hs.summable
  refine ⟨fun j ↦ (hi j).1, ho, ?_⟩
  have h := ho.tsum_le_tsum hj hs.summable
  rw [hs.tsum_eq] at h
  exact h.trans_eq (by dsimp [B]; ring)

end Mettapedia.Analysis.GeometricMinSeries
