import Init.Omega
import Mathlib.Tactic.NormNum

/-!
# Same-width exact ZAB obstruction: arithmetic budget facts

This module isolates the elementary arithmetic showing that the same-width
`n + 2k + 1` budget is smaller than the full exact visible surface whenever
the visible width is at least two.
-/

namespace Mettapedia.Computability.PNP

section Arithmetic

theorem sameWidthBudget_lt_surfaceCard_of_two_le_visibleWidth
    {n k : ℕ}
    (hvisible : 2 ≤ n + 2 * k) :
    n + 2 * k + 1 < 2 ^ (n + 2 * k) := by
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hvisible
  rw [hc]
  have h :
      ∀ d : ℕ, d + 3 < 2 ^ (d + 2) := by
    intro d
    induction d with
    | zero =>
        norm_num
    | succ d ih =>
        have hle : d + 4 ≤ 2 ^ (d + 2) := Nat.succ_le_of_lt ih
        have hltpow : 2 ^ (d + 2) < 2 ^ (d + 3) := by
          have hpos : 0 < 2 ^ (d + 2) := by
            exact pow_pos (by decide) _
          calc
            2 ^ (d + 2) < 2 ^ (d + 2) + 2 ^ (d + 2) := Nat.lt_add_of_pos_right hpos
            _ = 2 ^ (d + 3) := by
              rw [← two_mul, Nat.mul_comm]
              simp [Nat.pow_succ]
        exact lt_of_le_of_lt hle hltpow
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h c

theorem sameWidthExtractor_lt_truthTableGap_of_two_le_visibleWidth
    {n k : ℕ}
    (hvisible : 2 ≤ n + 2 * k) :
    n < 2 ^ (n + 2 * k) - (2 * k + 1) := by
  have hbudget :
      n + 2 * k + 1 < 2 ^ (n + 2 * k) :=
    sameWidthBudget_lt_surfaceCard_of_two_le_visibleWidth (n := n) (k := k) hvisible
  omega

end Arithmetic

end Mettapedia.Computability.PNP
