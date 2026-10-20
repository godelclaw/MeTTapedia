import Mettapedia.PLN.Evidence.BinaryEvidence

namespace Mettapedia.PLN.Evidence

open Classical

/-!
# Derived PLN Rules from BinaryEvidence

This file collects small, semantics-first facts:
- which PLN/NARS truth rules correspond directly to operations on the BinaryEvidence carrier, and
- the exact algebraic statements we have proven in Lean.

It is intentionally lightweight and does not depend on the probability-derivation files.
-/

namespace BinaryEvidence

/-! ## Negation-as-polarity-swap

PLN/NARS "negation" at the STV level typically maps `(s,c)` to `(1-s,c)`.
On BinaryEvidence counts `(n⁺, n⁻)`, the corresponding operation is swapping the components.

This is *not* Heyting negation `compl`; it is a polarity swap preserving total evidence.
-/

theorem swap_total (e : BinaryEvidence) : (swap e).total = e.total := by
  -- total is `pos + neg`, and addition is commutative.
  simp [swap, BinaryEvidence.total, add_comm]

theorem toStrength_swap (e : BinaryEvidence) (ht0 : e.total ≠ 0) (htT : e.total ≠ ⊤) :
    toStrength (swap e) = 1 - toStrength e := by
  -- Unfold `toStrength` and compute in `ℝ≥0∞`.
  unfold toStrength
  have hswap0 : (swap e).total ≠ 0 := by simpa [swap_total] using ht0
  -- Remove the `if` branches.
  simp only [ht0, hswap0, ↓reduceIte]
  -- Rewrite the swapped strength denominator to `e.total` and unfold the numerator.
  rw [swap_total]
  simp [swap]
  have hposT : e.pos ≠ (⊤ : ENNReal) := by
    intro h
    apply htT
    simp [BinaryEvidence.total, h]
  have h_total_sub : e.total - e.pos = e.neg := by
    -- `total = pos + neg`, and `pos` is finite, so we can cancel it.
    -- This is the `ENNReal`-specialized cancellation lemma.
    exact ENNReal.sub_eq_of_eq_add_rev hposT (by rfl)
  -- Push subtraction through division: (a - b)/c = a/c - b/c.
  have hsub : (e.total - e.pos) / e.total = e.total / e.total - e.pos / e.total := by
    simpa using (ENNReal.sub_div (a := e.total) (b := e.pos) (c := e.total) (h := fun _ _ => ht0))
  -- `neg/total = (total - pos)/total = 1 - pos/total`.
  rw [← h_total_sub, hsub, ENNReal.div_self ht0 htT]

end BinaryEvidence

end Mettapedia.PLN.Evidence
