import KrennFrozenCase0NoncollapseType01Chart3

/-!
A direct canonical exclusion inside type-01 pivot chart 3.

If `w_12_12` is live while `w_34_11` vanishes, row 181 forces
`w_35_11 = 0`.  The frozen amplitude row 360 then reduces to `Gb = 0`,
contradicting the non-collapse factor geometry.  This is a source-level
lemma: it does not depend on a branch certificate or on a solver trace.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3W12_12LiveW34Zero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.SparseCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- A live `w_12_12` and a zero `w_34_11` are incompatible with the
non-collapse type-01 chart-3 equations. -/
theorem refutes_chart3_w12_12_live_w34_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h12_12 : values 29 ≠ 0) (h34 : values 64 = 0) : False := by
  obtain ⟨_hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  have source181 : sourceValue values 181 = 0 := by
    apply base 181
    intro slot
    fin_cases slot <;> simp [determinantSourceIndex]
  have source181Shape : sourceValue values 181 = values 29 * values 70 := by
    rcases chart with ⟨_h23, _h12, h13⟩
    simp [sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h13, h34]
  rw [source181Shape] at source181
  have h35 : values 70 = 0 :=
    (mul_eq_zero.mp source181).resolve_left h12_12
  have source360 : sourceValue values 360 = 0 := by
    apply base 360
    intro slot
    fin_cases slot <;> simp [determinantSourceIndex]
  have source360Shape : sourceValue values 360 =
      values 23 * values 51 + values 15 * values 56 := by
    simp [sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h34, h35]
    ring
  rw [source360Shape] at source360
  apply hGb
  simpa [factorGb] using source360

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3W12_12LiveW34Zero.refutes_chart3_w12_12_live_w34_zero

end Krenn.FrozenCase0NoncollapseType01Chart3W12_12LiveW34Zero
