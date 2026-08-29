import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction
import KrennFrozenCase0NoncollapseType01Chart3SumzeroDirect

/-!
Direct canonical closure of the B0 face where both `w_15_11` and
`w_14_11` are live.

The external tree reaches a one-row `-1` leaf after two monomial closures.
Here the same fact follows from canonical rows 644, 645, and 745.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14Live

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 2 -> Fin 747 := ![644, 645]

theorem source_not_determinant
    (index : Fin 2) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- The live-`w_15_11` and live-`w_14_11` B0 face is empty. -/
theorem refutes_chart3_both_live_sum_nonzero_b0_w15_live_w14_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 ≠ 0) (h14 : values 42 ≠ 0) :
    False := by
  obtain ⟨h12_10, _, h12_12, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart h24 h25
  rcases chart with ⟨h23, h12, h13⟩
  have source644 : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have h02_11 : values 4 = 0 := by
    have identity : sourceValue values (sourceIndex 0) = values 4 * values 45 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01, h12, h13_10]
    rw [identity] at source644
    exact (mul_eq_zero.mp source644).resolve_right h15
  have source645 : sourceValue values (sourceIndex 1) = 0 :=
    base (sourceIndex 1) (source_not_determinant 1)
  have h03_11 : values 7 = 0 := by
    have identity : sourceValue values (sourceIndex 1) = values 7 * values 42 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01, h12_10, h13]
    rw [identity] at source645
    exact (mul_eq_zero.mp source645).resolve_right h14
  have source745 : sourceValue values 745 = 0 :=
    base 745 Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.source745_not_determinant
  rw [Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.source745_chart3_identity
      values ⟨h23, h12, h13⟩] at source745
  simp [h01, h02_11, h03_11] at source745

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14Live.refutes_chart3_both_live_sum_nonzero_b0_w15_live_w14_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14Live
