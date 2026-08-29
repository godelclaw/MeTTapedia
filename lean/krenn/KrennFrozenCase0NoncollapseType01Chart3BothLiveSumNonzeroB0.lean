import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14Zero
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveSource745
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveBalanced
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14Live
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroSource745
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroBalanced

/-!
Exhaustive closure of the B0 face of the type-01, chart-3, both-live,
nonzero-pivot-sum branch.

The proof names every binary face: first `w_34_11`, then `w_15_11`, then
`w_14_11`, with the two residual pivots split only where their corresponding
canonical argument needs them.  Thus no terminal leaf is implicit.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

theorem refutes_chart3_both_live_sum_nonzero_b0
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0) : False := by
  by_cases h34 : values 64 = 0
  · exact Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroBridge.refutes_chart3_both_live_sum_nonzero_b0_w34_zero
      values base hdet chart h24 h25 hsum h34
  by_cases h15 : values 45 = 0
  · by_cases h14 : values 42 = 0
    · exact Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14Zero.refutes_chart3_both_live_sum_nonzero_b0_w15_zero_w14_zero
        values base hdet chart h24 h25 hsum h15 h14
    by_cases h02_11 : values 4 = 0
    · exact Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveSource745.refutes_w02_11_zero
        values base hdet chart h24 h25 hsum h15 h14 h02_11
    exact Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveBalanced.refutes_w15_zero_w14_live_w02_11_live
      values base hdet chart h24 h25 hsum h15 h14 h02_11
  by_cases h14 : values 42 = 0
  · by_cases h03_11 : values 7 = 0
    · exact Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroSource745.refutes_w03_11_zero
        values base hdet chart h24 h25 hsum h15 h14 h03_11
    exact Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroBalanced.refutes_w15_live_w14_zero_w03_11_live
      values base hdet chart h24 h25 hsum h15 h14 h34 h03_11
  exact Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14Live.refutes_chart3_both_live_sum_nonzero_b0_w15_live_w14_live
    values base hdet chart h24 h25 hsum h15 h14

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0.refutes_chart3_both_live_sum_nonzero_b0

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0
