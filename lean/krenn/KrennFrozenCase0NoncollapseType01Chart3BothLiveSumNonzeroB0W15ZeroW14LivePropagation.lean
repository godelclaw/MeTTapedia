import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction

/-!
Canonical propagation for the B0 face with `w_15_11 = 0` and
`w_14_11 ≠ 0`.

The external monomial closure derives five coordinates from five canonical
amplitude rows.  This file states that propagation directly, so downstream
leaves can use named mathematical facts rather than an opaque closure log.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LivePropagation

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 5 -> Fin 747 := ![709, 362, 645, 532, 738]

theorem source_not_determinant
    (index : Fin 5) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- The exact five-coordinate propagation behind the recorded B0 monomial
closure in the `w_15_11 = 0`, `w_14_11 ≠ 0` child. -/
theorem forced_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 = 0) (h14 : values 42 ≠ 0) :
    values 6 = 0 ∧ values 49 = 0 ∧ values 7 = 0 ∧ values 8 = 0 ∧ values 47 = 0 := by
  obtain ⟨h12_10, h13_12, h12_12, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart h24 h25
  rcases chart with ⟨h23, h12, h13⟩
  have source709 : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have h03_00 : values 6 = 0 := by
    have identity : sourceValue values (sourceIndex 0) =
        values 6 * values 42 * values 56 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12, h15, h13_10]
    rw [identity] at source709
    have h : values 6 * values 42 = 0 :=
      (mul_eq_zero.mp source709).resolve_right h25
    exact (mul_eq_zero.mp h).resolve_right h14
  have source362 : sourceValue values (sourceIndex 1) = 0 :=
    base (sourceIndex 1) (source_not_determinant 1)
  have h23_22 : values 49 = 0 := by
    have identity : sourceValue values (sourceIndex 1) = values 42 * values 49 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12_12, h13_12, h15]
    rw [identity] at source362
    exact (mul_eq_zero.mp source362).resolve_left h14
  have source645 : sourceValue values (sourceIndex 2) = 0 :=
    base (sourceIndex 2) (source_not_determinant 2)
  have h03_11 : values 7 = 0 := by
    have identity : sourceValue values (sourceIndex 2) = values 7 * values 42 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01, h12_10, h13]
    rw [identity] at source645
    exact (mul_eq_zero.mp source645).resolve_right h14
  have source532 : sourceValue values (sourceIndex 3) = 0 :=
    base (sourceIndex 3) (source_not_determinant 3)
  have h03_22 : values 8 = 0 := by
    have identity : sourceValue values (sourceIndex 3) = values 8 * values 42 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12_10, h13_12]
    rw [identity] at source532
    exact (mul_eq_zero.mp source532).resolve_right h14
  have source738 : sourceValue values (sourceIndex 4) = 0 :=
    base (sourceIndex 4) (source_not_determinant 4)
  have h23_00 : values 47 = 0 := by
    have identity : sourceValue values (sourceIndex 4) = values 42 * values 47 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h03_00, h12_10, h13_10, h15]
    rw [identity] at source738
    exact (mul_eq_zero.mp source738).resolve_left h14
  exact ⟨h03_00, h23_22, h03_11, h03_22, h23_00⟩

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LivePropagation.forced_zeros

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LivePropagation
