import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumZero
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzero

/-!
Complete semantic closure of type-01 pivot chart 3.

The first pivot cover rules out the both-zero and one-pivot faces; the two
surviving live-pivot faces are partitioned by whether their pivot sum is
zero.  Both resulting branches are explicitly refuted.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3Full

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

theorem refutes_slot1_chart3
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values) : False := by
  obtain ⟨h24, h25, hsum | hsum⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLive.both_live_sum_cover_of_chart3
      values base hdet chart
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumZero.refutes_chart3_both_live_sum_zero
        values base hdet chart h24 h25 hsum
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzero.refutes_chart3_both_live_sum_nonzero
        values base hdet chart h24 h25 hsum

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3Full.refutes_slot1_chart3

end Krenn.FrozenCase0NoncollapseType01Chart3Full
