import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05_22Zero
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05Zero02Live22Bridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05Live02Live22Bridge

/-!
The strict W05 certificates eliminate the complete W05 carrier split.

The two semantic bridges on the `w_05_22 != 0` face do not use the historical
`w_05_00` branch.  Together with the already-closed `w_05_22 = 0` face, two
field case splits cover all eight W05 leaves.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

theorem refutes_chart3_b1_w05
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0) (h01 : values 1 ≠ 0)
    (h12_12 : values 29 = 0) : False := by
  by_cases h05_22 : values 24 = 0
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05_22Zero.refutes_chart3_b1_w05_22_zero
        values base hdet chart h24 h25 hsum h01 h12_12 h05_22
  by_cases h05_02 : values 18 = 0
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05Zero02Live22Bridge.refutes_chart3_b1_w05_02_zero_w05_22_live
        values base hdet chart h24 h25 hsum h01 h12_12 h05_02 h05_22
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05Live02Live22Bridge.refutes_chart3_b1_w05_02_w05_22_live
        values base hdet chart h24 h25 hsum h01 h12_12 h05_02 h05_22

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05.refutes_chart3_b1_w05

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05
