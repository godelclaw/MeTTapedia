import KrennFrozenCase0NoncollapseType01Chart3B2Z_W15Zero
import KrennFrozenCase0NoncollapseType01Chart3W14ZeroW15Live
import KrennFrozenCase0NoncollapseType01Chart3W01ZeroW15W14LiveDirect

/-!
The `w_01_11 = 0` half of the chart-3 `b2` branch.

This closes the formerly external `b2z / w15 != 0` leaf without importing
its reordered certificate: if `w_14_11 = 0`, live `w_15_11` contradicts
live `w_12_12`; if `w_14_11 != 0`, three canonical amplitude rows already
contradict the branch.  The `w_15_11 = 0` child remains the existing strict
certificate reflection.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B2Z

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- No point reaches the `b2` branch with `w_01_11 = 0`. -/
theorem refutes_chart3_b2_w01_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 = 0) (h12_12 : values 29 ≠ 0)
    (h12_10 : values 27 = 0) (h01 : values 1 = 0) : False := by
  by_cases h15 : values 45 = 0
  · exact Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15Zero.refutes_chart3_b2z_w15_zero
      values base hdet chart h24 h25 hsum h13_12 h12_12 h12_10 h01 h15
  · by_cases h14 : values 42 = 0
    · exact Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroW15Live.refutes_w14_zero_w15_live_w12_12_live
        values base hdet chart h24 h25 h14 h15 h12_12
    · exact Krenn.FrozenCase0NoncollapseType01Chart3W01ZeroW15W14LiveDirect.refutes_chart3_w01_zero_w12_10_zero_w15_w14_live
        values base hdet chart h24 h25 h01 h12_10 h15 h14

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B2Z.refutes_chart3_b2_w01_zero

end Krenn.FrozenCase0NoncollapseType01Chart3B2Z
