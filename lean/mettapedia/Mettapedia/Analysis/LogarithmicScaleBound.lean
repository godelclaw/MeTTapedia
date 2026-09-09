/-
SPDX-License-Identifier: Apache-2.0
Adapted from OpenAI, NavierStokesAndEuler, Euler/LogarithmicCutoffOptimization.lean.
Upstream revision: 8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538.
Modified by MeTTapedia contributors: arbitrary positive decay exponent,
explicit scale selection, sharper bound, and weaker sign assumptions.
See LICENSES/Apache-2.0.txt at the repository root.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Eliminating a small scale from a logarithmic estimate

An estimate with a low-frequency cost `L`, a logarithmic cost `W * (-log ε)`,
and a decaying high-frequency cost `ε ^ α * H` yields a logarithmic bound
in `H`. The exponent `α` is any positive real, rather than a fixed Sobolev
exponent. No sign assumption on `L` or `W` is needed for the sharp bound.

This is scalar analysis only: it does not assert a PDE continuation criterion
or a bound on any norm of an evolving solution.
-/

namespace Mettapedia.Analysis

open Real

/-- Choose a scale whose high-frequency cost is at most one and whose
logarithmic cost is explicit. -/
theorem exists_scale_rpow_mul_le_one {α H : ℝ} (hα : 0 < α) (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      -log ε = log (exp 1 + H) / α ∧ ε ^ α * H ≤ 1 := by
  let A := exp 1 + H
  have hE : 1 < exp (1 : ℝ) := by
    simpa only [exp_zero] using exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hA : 1 < A := by dsimp [A]; linarith
  have hApos : 0 < A := zero_lt_one.trans hA
  let ε := exp (-log A / α)
  have hεpos : 0 < ε := exp_pos _
  have hεlt : ε < 1 := by
    have hneg : -log A / α < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos (log_pos hA)) hα
    simpa only [ε, exp_zero] using exp_lt_exp.mpr hneg
  have hlog : -log ε = log A / α := by simp only [ε, log_exp]; ring
  have hpow : ε ^ α = A⁻¹ := by
    dsimp [ε]
    rw [rpow_def_of_pos (exp_pos _), log_exp,
      div_mul_cancel₀ _ (ne_of_gt hα), exp_neg, exp_log hApos]
  refine ⟨ε, hεpos, hεlt, hlog, ?_⟩
  rw [hpow, mul_comm, ← div_eq_mul_inv]
  exact (div_le_one hApos).mpr (le_add_of_nonneg_left (exp_pos 1).le)

/-- Remove the cutoff parameter from a low/logarithmic/high scale bound.
The coefficient of the logarithm records the exact loss `1 / α`. -/
theorem le_logarithmic_of_le_scale_bound {X C L W H α : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hα : 0 < α)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
      X ≤ C * (L + W * (-log ε) + ε ^ α * H)) :
    X ≤ C * (L + W * (log (exp 1 + H) / α) + 1) := by
  obtain ⟨ε, hεpos, hεlt, hlog, hhigh⟩ := exists_scale_rpow_mul_le_one hα hH
  have h := hbound ε hεpos hεlt
  rw [hlog] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hhigh) hC)

/-- The quarter-power specialization used by the whole-space logarithmic
gradient estimate. Only this coarser corollary needs `L ≥ 0`. -/
theorem le_four_mul_logarithmic_of_le_quarter_scale_bound {X C L W H : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
      X ≤ C * (L + W * (-log ε) + ε ^ (1 / 4 : ℝ) * H)) :
    X ≤ 4 * C * (1 + L + W * log (exp 1 + H)) := by
  have h := le_logarithmic_of_le_scale_bound hC hH (by norm_num : (0 : ℝ) < 1 / 4) hbound
  have hnonneg : 0 ≤ C * (3 + 3 * L) := mul_nonneg hC (by linarith)
  norm_num only [div_div, div_one] at h
  nlinarith only [h, hnonneg]

end Mettapedia.Analysis
