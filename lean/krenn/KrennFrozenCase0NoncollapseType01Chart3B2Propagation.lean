import KrennFrozenCase0NoncollapseType01Chart3

/-!
Reusable source-level propagation for the chart-3 `b2` branch.

The external `b2` monomial closure starts by removing `w_34_00` and
`w_05_22`.  Both vanish directly from canonical amplitude rows once the two
opposite pivots and `w_12_12` are live.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B2Propagation

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 2 → Fin 747 := ![46, 125]

theorem source_not_determinant
    (index : Fin 2) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- The two initial zeroes of the `b2` closure are canonical consequences,
not trusted preprocessing. -/
theorem b2_root_closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h12_12 : values 29 ≠ 0) :
    values 61 = 0 ∧ values 24 = 0 := by
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live
      values base hdet chart h24 h25
  have source0 : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have source1 : sourceValue values (sourceIndex 1) = 0 :=
    base (sourceIndex 1) (source_not_determinant 1)
  have h34_00 : values 61 = 0 := by
    have identity : sourceValue values (sourceIndex 0) =
        values 29 * values 61 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h13_10]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left h12_12
  have h05_22 : values 24 = 0 := by
    have identity : sourceValue values (sourceIndex 1) =
        values 24 * values 29 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h13_10]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_right h12_12
  exact ⟨h34_00, h05_22⟩

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B2Propagation.b2_root_closure_zeros

end Krenn.FrozenCase0NoncollapseType01Chart3B2Propagation
