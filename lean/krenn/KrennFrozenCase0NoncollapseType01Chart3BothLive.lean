import KrennFrozenCase0NoncollapseType01Chart3OnlyW25
import KrennFrozenCase0NoncollapseType01Chart3OnlyW24
import KrennFrozenCase0NoncollapseType01Chart3W12_10Live

/-!
The structural surviving interface for type-01 pivot chart 3.

The two one-pivot-live branches are already refuted.  Therefore every
remaining chart-3 witness has both opposite pivots live; its only next
top-level case distinction is whether their sum vanishes.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLive

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

theorem opposite_pivots_live_of_chart3
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values) :
    values 51 ≠ 0 ∧ values 56 ≠ 0 := by
  rcases opposite_pivot_cover values base hdet chart with
      onlyW25 | onlyW24 | bothLive
  · exact (Krenn.FrozenCase0NoncollapseType01Chart3OnlyW25.refutes_slot1_chart3_only_w25
      values base hdet chart onlyW25.1 onlyW25.2).elim
  · exact (Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24.refutes_slot1_chart3_only_w24
      values base hdet chart onlyW24.1 onlyW24.2).elim
  · exact bothLive

/-- The surviving chart-3 geometry, including the two live opposite pivots
and the canonical two-row consequence `w_12_10 = 0`. -/
theorem chart3_surviving_coordinates
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values) :
    values 51 ≠ 0 ∧ values 56 ≠ 0 ∧ values 27 = 0 := by
  obtain ⟨h24, h25⟩ := opposite_pivots_live_of_chart3 values base hdet chart
  exact ⟨h24, h25,
    Krenn.FrozenCase0NoncollapseType01Chart3W12_10Live.w12_10_zero_of_chart3
      values base hdet chart⟩

/-- The exhaustive remaining top-level split after the two one-pivot
branches and the both-zero branch have been eliminated. -/
theorem both_live_sum_cover_of_chart3
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values) :
    values 51 ≠ 0 ∧ values 56 ≠ 0 ∧
      (values 51 + values 56 = 0 ∨ values 51 + values 56 ≠ 0) := by
  obtain ⟨h24, h25⟩ := opposite_pivots_live_of_chart3 values base hdet chart
  exact ⟨h24, h25, eq_or_ne (values 51 + values 56) 0⟩

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLive.opposite_pivots_live_of_chart3
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLive.chart3_surviving_coordinates
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLive.both_live_sum_cover_of_chart3

end Krenn.FrozenCase0NoncollapseType01Chart3BothLive
