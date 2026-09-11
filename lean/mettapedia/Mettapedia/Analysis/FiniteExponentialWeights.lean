import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite exponential weights and their square-root amplitudes

The weights are strictly positive and sum to one. Their mean score is at
most `log(card)` below any individual score. Equivalently, exponential
weights on negative costs lose at most temperature times `log(card)`
relative to the least cost. No spatial support is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteExponentialWeights

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def partition (s : ι → ℝ) : ℝ := ∑ i, Real.exp (s i)

def weight (s : ι → ℝ) (i : ι) : ℝ := Real.exp (s i) / partition s

def amplitude (s : ι → ℝ) (i : ι) : ℝ := Real.exp (s i / 2) / Real.sqrt (partition s)

def mean (s v : ι → ℝ) : ℝ := ∑ i, weight s i * v i

theorem partition_pos (s : ι → ℝ) : 0 < partition s :=
  Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty

theorem weight_pos (s : ι → ℝ) (i : ι) : 0 < weight s i :=
  div_pos (Real.exp_pos _) (partition_pos s)

theorem sum_weight (s : ι → ℝ) : (∑ i, weight s i) = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos s))

theorem amplitude_pos (s : ι → ℝ) (i : ι) : 0 < amplitude s i :=
  div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (partition_pos s))

theorem mean_const (s : ι → ℝ) (c : ℝ) : mean s (fun _ ↦ c) = c := by
  simp only [mean, ← Finset.sum_mul, sum_weight, one_mul]

theorem mean_add_const (s v : ι → ℝ) (c : ℝ) :
    mean s (fun i ↦ v i + c) = mean s v + c := by
  simp only [mean, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_weight, one_mul]

theorem amplitude_sq (s : ι → ℝ) (i : ι) : amplitude s i ^ 2 = weight s i := by
  rw [amplitude, div_pow, Real.sq_sqrt (partition_pos s).le, ← Real.exp_nat_mul]
  congr 2
  ring

theorem sum_amplitude_sq (s : ι → ℝ) : (∑ i, amplitude s i ^ 2) = 1 := by
  simp_rw [amplitude_sq]
  exact sum_weight s

theorem log_weight (s : ι → ℝ) (i : ι) : Real.log (weight s i) = s i - Real.log (partition s) := by
  rw [weight, Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (partition_pos s)), Real.log_exp]

/-- The entropy bound is proved directly from `log x ≤ x - 1`. -/
theorem neg_sum_mul_log_le (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, p i) = 1) :
    -(∑ i, p i * Real.log (p i)) ≤ Real.log (Fintype.card ι) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hi (i : ι) :
      -(p i * Real.log (p i)) ≤ p i * Real.log (Fintype.card ι) + 1 / Fintype.card ι - p i := by
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (inv_pos.mpr (mul_pos hN (hp i)))) (hp i).le
    rw [Real.log_inv, Real.log_mul (ne_of_gt hN) (ne_of_gt (hp i))] at h
    have hid : p i * ((Fintype.card ι : ℝ) * p i)⁻¹ = 1 / Fintype.card ι := by
      field_simp [ne_of_gt (hp i)]
    nlinarith only [h, hid]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
  simp only [Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum, one_mul] at h
  have hid : (Fintype.card ι : ℝ) * (1 / Fintype.card ι) = 1 := by field_simp
  linarith only [h, hid]

theorem mean_score_ge (s : ι → ℝ) (j : ι) :
    s j - Real.log (Fintype.card ι) ≤ mean s s := by
  have h := neg_sum_mul_log_le (weight s) (weight_pos s) (sum_weight s)
  simp_rw [log_weight, mul_sub] at h
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_weight, one_mul] at h
  have hj : Real.exp (s j) ≤ partition s :=
    Finset.single_le_sum (fun i _ ↦ (Real.exp_pos _).le) (Finset.mem_univ j)
  have hlog := Real.log_le_log (Real.exp_pos _) hj
  rw [Real.log_exp] at hlog
  unfold mean
  linarith only [h, hlog]

theorem mean_cost_le (cost : ι → ℝ) (tau : ℝ) (ht : 0 < tau) (j : ι) :
    mean (fun i ↦ -cost i / tau) cost ≤ cost j + tau * Real.log (Fintype.card ι) := by
  have h := mul_le_mul_of_nonneg_left (mean_score_ge (fun i ↦ -cost i / tau) j) ht.le
  have hid : mean (fun i ↦ -cost i / tau) (fun i ↦ -cost i / tau) =
      -(mean (fun i ↦ -cost i / tau) cost) / tau := by
    unfold mean
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid] at h
  have ht0 := ne_of_gt ht
  have hcancel (r : ℝ) : tau * (r / tau) = r := by field_simp
  rw [mul_sub, hcancel, hcancel] at h
  nlinarith only [h]

end Mettapedia.Analysis.FiniteExponentialWeights
