import KrennFrozenCase0NoncollapseType01Chart3

/-!
A direct non-collapse exclusion for the live `w_12_10` branch of pivot
chart 3.

Canonical rows 360 and 298 form a two-row syzygy.  In chart 3 their
difference, after multiplying row 360 by `w_12_10`, is exactly
`w_12_10 * Gb`.  The non-collapse factor geometry makes `Gb` nonzero, so a
live `w_12_10` is impossible.  This is independent of the later opposite
pivot and pivot-sum splits.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3W12_10Live

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 2 -> Fin 747 := ![360, 298]

theorem source_not_determinant
    (index : Fin 2) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- In pivot chart 3, non-collapse forces `w_12_10 = 0`. -/
theorem w12_10_zero_of_chart3
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values) : values 27 = 0 := by
  rcases chart with ⟨_h23, _h12, h13⟩
  obtain ⟨_hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  have source360 : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have source298 : sourceValue values (sourceIndex 1) = 0 :=
    base (sourceIndex 1) (source_not_determinant 1)
  have identity : values 27 * factorGb values =
      values 27 * sourceValue values (sourceIndex 0) -
        sourceValue values (sourceIndex 1) := by
    simp [sourceValue, sourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      factorGb, h13]
    ring
  have productZero : values 27 * factorGb values = 0 := by
    rw [identity, source360, source298]
    ring
  exact (mul_eq_zero.mp productZero).resolve_right hGb

/-- A contradiction form for any descendant declaring `w_12_10` live. -/
theorem refutes_chart3_w12_10_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h12_10 : values 27 ≠ 0) : False := by
  exact h12_10 (w12_10_zero_of_chart3 values base hdet chart)

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W12_10Live.w12_10_zero_of_chart3
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W12_10Live.refutes_chart3_w12_10_live

end Krenn.FrozenCase0NoncollapseType01Chart3W12_10Live
