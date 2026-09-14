import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Disjoint dyadic shells of the integer lattice

The shell index is the base-two logarithm of the largest absolute
coordinate. Every nonzero lattice point belongs to exactly one shell.
The three-dimensional cardinality bound is explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.IntegerDyadicShell

open scoped BigOperators ENNReal

abbrev Lattice := Fin 3 → ℤ

def height (q : Lattice) : ℕ := Finset.univ.sup (fun i ↦ (q i).natAbs)

def index (q : Lattice) : ℕ := Nat.log 2 (height q)

def cube (N : ℕ) : Finset Lattice :=
  Fintype.piFinset (fun _ ↦ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)))

def shell (n : ℕ) : Finset Lattice :=
  (cube (2 ^ n)).filter (fun q ↦ 2 ^ n ≤ height q ∧ height q < 2 ^ (n + 1))

theorem coordinate_le_height (q : Lattice) (i : Fin 3) : (q i).natAbs ≤ height q :=
  Finset.le_sup (f := fun i ↦ (q i).natAbs) (Finset.mem_univ i)

theorem height_eq_zero_iff (q : Lattice) : height q = 0 ↔ q = 0 := by
  constructor
  · intro h
    ext i
    have hi := coordinate_le_height q i
    rw [h] at hi
    exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hi)
  · rintro rfl
    apply Nat.eq_zero_of_le_zero
    exact Finset.sup_le (fun i _ ↦ by simp)

theorem mem_cube (N : ℕ) (q : Lattice) :
    q ∈ cube N ↔ ∀ i, |q i| ≤ 2 * (N : ℤ) := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le]

theorem mem_shell (n : ℕ) (q : Lattice) :
    q ∈ shell n ↔ 2 ^ n ≤ height q ∧ height q < 2 ^ (n + 1) := by
  rw [shell, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  rw [mem_cube]
  intro i
  have hi := (coordinate_le_height q i).trans_lt h.2
  rw [pow_succ] at hi
  have hc : (q i).natAbs ≤ 2 * 2 ^ n := by omega
  rw [← Int.natCast_natAbs]
  exact_mod_cast hc

theorem ne_zero_of_mem_shell {n : ℕ} {q : Lattice} (hq : q ∈ shell n) : q ≠ 0 := by
  intro hz
  have h := (mem_shell n q).mp hq
  rw [← height_eq_zero_iff] at hz
  rw [hz] at h
  have hp : 0 < (2 : ℕ) ^ n := by positivity
  omega

theorem mem_shell_index (q : Lattice) (hq : q ≠ 0) : q ∈ shell (index q) := by
  rw [mem_shell]
  exact ⟨Nat.pow_log_le_self 2 (mt (height_eq_zero_iff q).mp hq),
    Nat.lt_pow_succ_log_self (by norm_num) _⟩

theorem index_eq_of_mem_shell {n : ℕ} {q : Lattice} (hq : q ∈ shell n) : index q = n := by
  have h := (mem_shell n q).mp hq
  exact Nat.log_eq_of_pow_le_of_lt_pow h.1 h.2

theorem mem_shell_iff (n : ℕ) (q : Lattice) : q ∈ shell n ↔ q ≠ 0 ∧ index q = n := by
  constructor
  · exact fun h ↦ ⟨ne_zero_of_mem_shell h, index_eq_of_mem_shell h⟩
  · rintro ⟨hq, rfl⟩
    exact mem_shell_index q hq

theorem card_cube (N : ℕ) : (cube N).card = (4 * N + 1) ^ 3 := by
  rw [cube, Fintype.card_piFinset_const, Int.card_Icc]
  congr 1
  omega

theorem card_shell_le (n : ℕ) : (shell n).card ≤ 125 * (2 ^ n) ^ 3 := by
  have h := Finset.card_le_card (Finset.filter_subset (s := cube (2 ^ n))
    (p := fun q ↦ 2 ^ n ≤ height q ∧ height q < 2 ^ (n + 1)))
  rw [card_cube] at h
  apply h.trans
  have hp : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow n 2 (by omega)
  calc
    (4 * 2 ^ n + 1) ^ 3 ≤ (5 * 2 ^ n) ^ 3 := by gcongr; omega
    _ = _ := by ring

/-- Extended sums require no summability assumption; the zero mode is separate. -/
theorem tsum_shells (f : Lattice → ℝ≥0∞) (hzero : f 0 = 0) :
    (∑' n, ∑ q ∈ shell n, f q) = ∑' q, f q := by
  have hf (n : ℕ) : (∑ q ∈ shell n, f q) =
      ∑' q : index ⁻¹' {n}, f q := by
    rw [tsum_subtype, sum_eq_tsum_indicator]
    apply tsum_congr
    intro q
    by_cases hq : q = 0
    · subst q
      simp [hzero, Set.indicator]
    · simp [Set.indicator, mem_shell_iff, hq]
  simp_rw [hf]
  exact ENNReal.tsum_fiberwise f index

theorem tsum_shells_le (f : Lattice → ℝ≥0∞) :
    (∑' n, ∑ q ∈ shell n, f q) ≤ ∑' q, f q := by
  let f' := fun q ↦ if q = 0 then 0 else f q
  have hzero : f' 0 = 0 := by simp [f']
  have he (n : ℕ) : (∑ q ∈ shell n, f q) = ∑ q ∈ shell n, f' q := by
    apply Finset.sum_congr rfl
    intro q hq
    simp [f', ne_zero_of_mem_shell hq]
  simp_rw [he]
  rw [tsum_shells f' hzero]
  exact ENNReal.tsum_le_tsum (fun q ↦ by dsimp [f']; split_ifs <;> simp)

/-- A summable allocation of the total budget to all dyadic scales. -/
def summationWeight (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * (n + 2))

theorem summationWeight_pos (n : ℕ) : 0 < summationWeight n := by
  unfold summationWeight
  positivity

theorem sum_summationWeight (N : ℕ) :
    (∑ n ∈ Finset.range N, summationWeight n) = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold summationWeight
    push_cast
    field_simp
    ring

theorem hasSum_summationWeight : HasSum summationWeight 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ (summationWeight_pos n).le) 1).mpr
  simp_rw [sum_summationWeight]
  simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem tsum_ofReal_summationWeight : (∑' n, ENNReal.ofReal (summationWeight n)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ (summationWeight_pos n).le)
    hasSum_summationWeight.summable, hasSum_summationWeight.tsum_eq]
  norm_num

end Mettapedia.Analysis.IntegerDyadicShell
