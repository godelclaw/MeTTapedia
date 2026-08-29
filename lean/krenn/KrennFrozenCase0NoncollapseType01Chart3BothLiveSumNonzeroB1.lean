import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05

/-!
The semantic attachment of the complete W05 carrier cover to its actual
parent: branch B1 of the nonzero-sum chart-3 split.

B1 is not a label assumed from an external tree.  Its first coordinate
`w_12_10` is canonically zero on chart 3; the two remaining defining facts
are `w_12_12 = 0` and `w_01_11 ≠ 0`.  The W05 theorem now eliminates this
whole face without retaining any of the historical W34 or W05 leaf facts.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- The B1 face of the live-pivots, nonzero-sum chart-3 branch has no common
zero.  The canonical `w_12_10 = 0` fact identifies this with the historical
B1 coordinate branch; no W34 or W05 split assumption remains. -/
theorem refutes_chart3_both_live_sum_nonzero_b1
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h12_12 : values 29 = 0) (h01 : values 1 ≠ 0) : False := by
  exact
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05.refutes_chart3_b1_w05
      values base hdet chart h24 h25 hsum h01 h12_12

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1.refutes_chart3_both_live_sum_nonzero_b1

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1
