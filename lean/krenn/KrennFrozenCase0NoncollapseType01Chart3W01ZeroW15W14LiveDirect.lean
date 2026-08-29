import KrennFrozenCase0NoncollapseType01Chart3SumzeroDirect

/-!
A three-row canonical closure for a broad chart-3 terminal family.

It subsumes the external sum-zero B0 branch with `w_01_11 = 0`,
`w_12_10 = 0`, and both `w_15_11` and `w_14_11` live.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3W01ZeroW15W14LiveDirect

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 2 -> Fin 747 := ![644, 645]

theorem source_not_determinant
    (index : Fin 2) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- In chart 3, this coordinate pattern is impossible.  The proof needs only
three canonical amplitude rows: 644 forces `w_02_11 = 0`, 645 forces
`w_03_11 = 0`, and 745 then becomes `-1 = 0`. -/
theorem refutes_chart3_w01_zero_w12_10_zero_w15_w14_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h01 : values 1 = 0) (h12_10 : values 27 = 0)
    (h15 : values 45 ≠ 0) (h14 : values 42 ≠ 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live
      values base hdet ⟨h23, h12, h13⟩ h24 h25

  have source644 : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have h02_11 : values 4 = 0 := by
    have identity : sourceValue values (sourceIndex 0) = values 4 * values 45 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01, h13_10, h12]
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
    base 745 source745_not_determinant
  have contradiction : sourceValue values 745 = -1 := by
    rw [source745_chart3_identity values ⟨h23, h12, h13⟩]
    simp [h01, h02_11, h03_11]
  rw [contradiction] at source745
  norm_num at source745

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W01ZeroW15W14LiveDirect.refutes_chart3_w01_zero_w12_10_zero_w15_w14_live

end Krenn.FrozenCase0NoncollapseType01Chart3W01ZeroW15W14LiveDirect
