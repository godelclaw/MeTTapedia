import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction
import KrennFrozenCase0NoncollapseType01Chart3SumzeroDirect

/-!
The canonical row-745 reduction for the live-`w_15_11`, zero-`w_14_11`
B0 face.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroSource745

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem source644_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ (644 : Fin 747) := by
  fin_cases slot <;> simp [determinantSourceIndex]

/-- In the live-`w_15_11` B0 face, canonical row 644 forces
`w_02_11 = 0`. -/
theorem w02_11_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 ≠ 0) :
    values 4 = 0 := by
  obtain ⟨_, _, _, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart h24 h25
  rcases chart with ⟨_, h12, _⟩
  have source644 : sourceValue values 644 = 0 := base 644 source644_not_determinant
  have identity : sourceValue values 644 = values 4 * values 45 := by
    simp [sourceValue, Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h01, h12, h13_10]
  rw [identity] at source644
  exact (mul_eq_zero.mp source644).resolve_right h15

/-- The subface with `w_03_11 = 0` is immediately contradictory by canonical
row 745. -/
theorem refutes_w03_11_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 ≠ 0) (h14 : values 42 = 0)
    (h03_11 : values 7 = 0) : False := by
  obtain ⟨_, _, _, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  have h02_11 : values 4 = 0 :=
    w02_11_zero values base hdet chart h24 h25 hsum h15
  rcases chart with ⟨h23, h12, h13⟩
  have source745 : sourceValue values 745 = 0 :=
    base 745 Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.source745_not_determinant
  rw [Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.source745_chart3_identity
      values ⟨h23, h12, h13⟩] at source745
  simp [h01, h02_11, h03_11, h14] at source745

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroSource745.w02_11_zero
#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroSource745.refutes_w03_11_zero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroSource745
