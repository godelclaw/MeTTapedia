import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0

/-!
The complete nonzero-pivot-sum face of the type-01 chart-3 branch.

The historical B0 tree has been semantically discharged from the canonical
chart hypotheses, so no external branch-label premise remains here.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

theorem refutes_chart3_both_live_sum_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0) : False := by
  exact
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0.refutes_chart3_both_live_sum_nonzero_b0
      values base hdet chart h24 h25 hsum

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzero.refutes_chart3_both_live_sum_nonzero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzero
