import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroBridge

/-!
Top-level semantic cover for the live-`w_12_12` half of chart 3's
both-opposite-pivots-live, nonzero-sum branch.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW12_12Live

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- Once `w_12_12` is live, the remaining `w_01_11` dichotomy is exhaustive:
the zero side is B2 and the live side is B3. -/
theorem refutes_chart3_both_live_sum_nonzero_w12_12_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h12_12 : values 29 ≠ 0) : False := by
  by_cases h01 : values 1 = 0
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroBridge.refutes_chart3_both_live_sum_nonzero_b2_w12_12_live
        values base hdet chart h24 h25 hsum h01 h12_12
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroBridge.refutes_chart3_both_live_sum_nonzero_b3_w12_12_live
        values base hdet chart h24 h25 hsum h01 h12_12

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW12_12Live.refutes_chart3_both_live_sum_nonzero_w12_12_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW12_12Live
