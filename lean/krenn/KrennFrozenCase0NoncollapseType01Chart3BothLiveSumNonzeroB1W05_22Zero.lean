import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05ZeroPairBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05Live02Zero22Bridge

/-!
The two strict W05 certificates eliminate the whole w05_22 = 0 face.

The external carrier tree split additionally on w05_00 and w05_02. The
attached source-provenance bridges show that neither certificate needs the
w05_00 split. A single field case split on w05_02 therefore covers all four
historical leaves with w05_22 = 0.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05_22Zero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

theorem refutes_chart3_b1_w05_22_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0) (h01 : values 1 ≠ 0)
    (h12_12 : values 29 = 0)
    (h05_22 : values 24 = 0) : False := by
  by_cases h05_02 : values 18 = 0
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05ZeroPairBridge.refutes_chart3_b1_w05_02_w05_22_zero
        values base hdet chart h24 h25 hsum h01 h12_12 h05_02 h05_22
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05Live02Zero22Bridge.refutes_chart3_b1_w05_02_live_w05_22_zero
        values base hdet chart h24 h25 hsum h01 h12_12 h05_02 h05_22

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05_22Zero.refutes_chart3_b1_w05_22_zero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05_22Zero
