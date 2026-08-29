import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction

/-!
Canonical propagation for the final B0 face with live `w_15_11`, zero
`w_14_11`, and live `w_34_11`.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroPropagation

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 5 -> Fin 747 := ![687, 709, 362, 714, 738]

theorem source_not_determinant
    (index : Fin 5) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- The five zeroes of the surviving live-`w_15_11`, zero-`w_14_11` B0 face,
obtained directly from canonical rows 687, 709, 362, 714, and 738. -/
theorem forced_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 ≠ 0) (h14 : values 42 = 0)
    (h34 : values 64 ≠ 0) :
    values 3 = 0 ∧ values 6 = 0 ∧ values 49 = 0 ∧ values 8 = 0 ∧ values 47 = 0 := by
  obtain ⟨h12_10, h13_12, h12_12, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart h24 h25
  rcases chart with ⟨h23, h12, h13⟩
  have source687 : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have h02_00 : values 3 = 0 := by
    have identity : sourceValue values (sourceIndex 0) = values 3 * values 45 * values 64 := by
      simp [sourceValue, sourceIndex, Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12_10, h13, h14]
    rw [identity] at source687
    by_contra h02_00
    have product_zero : values 3 * values 45 = 0 :=
      (mul_eq_zero.mp source687).resolve_right h34
    exact h15 ((mul_eq_zero.mp product_zero).resolve_left h02_00)
  have source709 : sourceValue values (sourceIndex 1) = 0 :=
    base (sourceIndex 1) (source_not_determinant 1)
  have h03_00 : values 6 = 0 := by
    have identity : sourceValue values (sourceIndex 1) = values 6 * values 45 * values 51 := by
      simp [sourceValue, sourceIndex, Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12, h13_10, h14]
    rw [identity] at source709
    by_contra h03_00
    have product_zero : values 6 * values 45 = 0 :=
      (mul_eq_zero.mp source709).resolve_right h24
    exact h15 ((mul_eq_zero.mp product_zero).resolve_left h03_00)
  have source362 : sourceValue values (sourceIndex 2) = 0 :=
    base (sourceIndex 2) (source_not_determinant 2)
  have h23_22 : values 49 = 0 := by
    have identity : sourceValue values (sourceIndex 2) = values 45 * values 49 := by
      simp [sourceValue, sourceIndex, Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12_12, h13_12, h14]
    rw [identity] at source362
    exact (mul_eq_zero.mp source362).resolve_left h15
  have source714 : sourceValue values (sourceIndex 3) = 0 :=
    base (sourceIndex 3) (source_not_determinant 3)
  have h03_22 : values 8 = 0 := by
    have identity : sourceValue values (sourceIndex 3) = values 8 * values 45 * values 51 := by
      simp [sourceValue, sourceIndex, Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12, h13_12, h14]
    rw [identity] at source714
    by_contra h03_22
    have product_zero : values 8 * values 45 = 0 :=
      (mul_eq_zero.mp source714).resolve_right h24
    exact h15 ((mul_eq_zero.mp product_zero).resolve_left h03_22)
  have source738 : sourceValue values (sourceIndex 4) = 0 :=
    base (sourceIndex 4) (source_not_determinant 4)
  have h23_00 : values 47 = 0 := by
    have identity : sourceValue values (sourceIndex 4) = values 45 * values 47 := by
      simp [sourceValue, sourceIndex, Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h02_00, h03_00, h12_10, h13_10, h14]
    rw [identity] at source738
    exact (mul_eq_zero.mp source738).resolve_left h15
  exact ⟨h02_00, h03_00, h23_22, h03_22, h23_00⟩

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroPropagation.forced_zeros

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroPropagation
