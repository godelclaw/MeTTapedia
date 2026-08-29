import KrennFrozenCase0NoncollapseType01Chart1
import KrennFrozenCase0NoncollapseType01Chart3Full

/-!
The remaining semantic reduction for non-collapse type 01.

The four priority pivot charts are exhaustive.  Charts 1, 2, and 3 are now
closed from the frozen base equations, so any hypothetical slot-1
non-collapse witness must lie in the sole remaining chart `w_23_11 != 0`.
-/

namespace Krenn.FrozenCase0NoncollapseType01PivotReduction

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot

theorem survivor_is_pivot_chart0
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0) :
    PivotChart0 values := by
  rcases pivot_cover values with chart0 | chart1 | chart2 | chart3
  · exact chart0
  · exact
      (Krenn.FrozenCase0NoncollapseType01Chart1.refutes_slot1_pivot_chart1
        values base hdet chart1).elim
  · exact (refutes_slot1_pivot_chart2 values base hdet chart2).elim
  · exact
      (Krenn.FrozenCase0NoncollapseType01Chart3Full.refutes_slot1_chart3
        values base hdet chart3).elim

#print axioms
  Krenn.FrozenCase0NoncollapseType01PivotReduction.survivor_is_pivot_chart0

end Krenn.FrozenCase0NoncollapseType01PivotReduction
