import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LivePropagation
import KrennFrozenCase0NoncollapseType01Chart3SumzeroDirect

/-!
The canonical row-745 endpoint for the B0 `w_15_11 = 0`,
`w_14_11 ≠ 0` propagation face.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveSource745

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Canonical row 687 is a non-determinant amplitude row. -/
theorem source687_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ (687 : Fin 747) := by
  fin_cases slot <;> simp [determinantSourceIndex]

/-- On this face, canonical row 745 has exactly one live monomial besides its
constant term. -/
theorem source745_reduced
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 = 0) (h14 : values 42 ≠ 0) :
    sourceValue values 745 = values 4 * values 42 * values 70 - 1 := by
  obtain ⟨_, _, _, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  obtain ⟨_, _, h03_11, _, _⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LivePropagation.forced_zeros
      values base hdet chart h24 h25 hsum h15 h14
  rw [Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.source745_chart3_identity values chart]
  simp [h01, h15, h03_11]

/-- The `w_02_11 = 0` child of this face is contradictory directly from
canonical row 745.  The tree's additional `w_02_00 = 0` split literal is not
needed. -/
theorem refutes_w02_11_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 = 0) (h14 : values 42 ≠ 0)
    (h02_11 : values 4 = 0) : False := by
  have source : sourceValue values 745 = 0 :=
    base 745 Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.source745_not_determinant
  rw [source745_reduced values base hdet chart h24 h25 hsum h15 h14, h02_11] at source
  norm_num at source

/-- If `w_02_00` is live on this face, row 687 forces `w_35_11 = 0`;
row 745 then supplies the contradiction.  Thus this closure also avoids the
external three-coordinate monomial log. -/
theorem refutes_w02_00_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 = 0) (h14 : values 42 ≠ 0)
    (h02_00 : values 3 ≠ 0) : False := by
  obtain ⟨h12_10, _, _, _⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  rcases chart with ⟨h23, h12, h13⟩
  have source687 : sourceValue values 687 = 0 :=
    base 687 source687_not_determinant
  have h35_11 : values 70 = 0 := by
    have identity : sourceValue values 687 = values 3 * values 42 * values 70 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12_10, h13, h15]
    rw [identity] at source687
    by_contra h35_11
    have product_zero : values 3 * values 42 = 0 :=
      (mul_eq_zero.mp source687).resolve_right h35_11
    exact h14 ((mul_eq_zero.mp product_zero).resolve_left h02_00)
  have source745 : sourceValue values 745 = 0 :=
    base 745 Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.source745_not_determinant
  rw [source745_reduced values base hdet ⟨h23, h12, h13⟩ h24 h25 hsum h15 h14,
      h35_11] at source745
  norm_num at source745

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveSource745.source745_reduced
#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveSource745.refutes_w02_11_zero
#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveSource745.refutes_w02_00_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveSource745
