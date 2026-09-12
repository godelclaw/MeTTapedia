import Mettapedia.Analysis.AnnularRieszKernel
import Mettapedia.Analysis.UnitTorusLattice
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Int.Interval

/-! # Finite lattice support of partial annular Riesz multipliers -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AnnularRieszKernel

open UnitTorusLattice
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem weight_eq_zero_of_le_norm (N : ℕ) (x : Rd)
    (hx : (2 : ℝ) ^ (N + 1) ≤ ‖x‖) : weight N x = 0 := by
  unfold weight
  apply Finset.sum_eq_zero
  intro n hn
  apply DyadicAnnulus.normalizedCutoff_eq_zero_of_le_norm
  have hnN : n + 1 ≤ N + 1 := by simpa using (Finset.mem_range.mp hn).le
  have hp : (2 : ℝ) ^ (n + 1) ≤ ‖x‖ :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnN).trans hx
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), one_div_pow]
  rw [pow_succ] at hp
  have hpos : 0 < (2 : ℝ) ^ n := by positivity
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ hpos).mpr
  nlinarith

/-- A finite coordinate box containing every nonzero partial multiplier. -/
def frequencySupport (N : ℕ) : Finset (Fin d → ℤ) :=
  Finset.Icc (fun _ ↦ -((2 : ℤ) ^ (N + 1))) (fun _ ↦ (2 : ℤ) ^ (N + 1))

theorem weight_frequency_eq_zero_of_not_mem (N : ℕ) (k : Fin d → ℤ)
    (hk : k ∉ frequencySupport N) : weight N (frequency k) = 0 := by
  apply weight_eq_zero_of_le_norm
  by_contra hn
  have hnorm : ‖frequency k‖ < (2 : ℝ) ^ (N + 1) := lt_of_not_ge hn
  apply hk
  rw [frequencySupport, Finset.mem_Icc]
  constructor <;> intro i
  · have hi := (PiLp.norm_apply_le (frequency k) i).trans hnorm.le
    have hb : -((2 : ℝ) ^ (N + 1)) ≤ (k i : ℝ) := by
      simpa [frequency, Real.norm_eq_abs, abs_le] using (abs_le.mp hi).1
    exact_mod_cast hb
  · have hi := (PiLp.norm_apply_le (frequency k) i).trans hnorm.le
    have hb : (k i : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
      simpa [frequency, Real.norm_eq_abs, abs_le] using (abs_le.mp hi).2
    exact_mod_cast hb

end Mettapedia.Analysis.AnnularRieszKernel
