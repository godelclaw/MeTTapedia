import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW12_12Live

/-!
The full live-`w_01_11` half of the nonzero-sum chart-3 branch.

The `w_12_12 = 0` face is B1, while its live complement is already closed by
the B2/B3 cover.  This is an ordinary field dichotomy, so it attaches the
new B1 theorem to the surrounding semantic branch rather than merely naming
another historical leaf.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW01Live

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- A nonzero-sum chart-3 witness cannot have `w_01_11` live. -/
theorem refutes_chart3_both_live_sum_nonzero_w01_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 ≠ 0) : False := by
  by_cases h12_12 : values 29 = 0
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1.refutes_chart3_both_live_sum_nonzero_b1
        values base hdet chart h24 h25 hsum h12_12 h01
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW12_12Live.refutes_chart3_both_live_sum_nonzero_w12_12_live
        values base hdet chart h24 h25 hsum h12_12

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW01Live.refutes_chart3_both_live_sum_nonzero_w01_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW01Live
