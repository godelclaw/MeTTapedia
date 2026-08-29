import KrennFrozenCase0NoncollapseAssembly
import KrennFrozenCase0NoncollapseType01PivotReduction

/-!
The completed type-01 pivot charts consume one of the eighteen non-collapse
slots. Charts 1, 2, and 3 are contradictory, so slot 1 is reduced exactly to
the remaining chart 0 condition `w_23_11 ≠ 0`.

This module deliberately does not assert the chart-0 contradiction. It exposes
that obligation as a typed input and connects any future proof of it to the
uniform eighteen-slot interface used by the frozen case-0 assembly.
-/

namespace Krenn.FrozenCase0NoncollapseType01Assembly

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseAssembly
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01PivotReduction

/-- The numeric coordinate defining chart 0 is bound to the frozen variable
inventory rather than justified only by a source comment. -/
theorem pivot_chart0_coordinate_name :
    Krenn.FrozenCase0System.variableNames 48 = "w_23_11" := by
  decide

/-- The sole surviving obligation for physical non-collapse slot 1 after the
four exhaustive type-01 pivot charts are reduced. -/
def RefutesPivotChart0 {R : Type*} [Field R] [CharZero R] : Prop :=
  ∀ (values : Fin 75 → R), BaseCommonZero values →
    slotDeterminant values 1 ≠ 0 → PivotChart0 values → False

/-- Charts 1, 2, and 3 are already impossible. Therefore a contradiction on
chart 0 supplies the exact slot-1 entry required by the non-collapse table. -/
theorem refutes_noncollapse_slot_one_of_pivot_chart0
    {R : Type*} [Field R] [CharZero R]
    (chart0 : RefutesPivotChart0 (R := R)) :
    RefutesNoncollapseSlot (R := R) 1 := by
  intro values base hdet
  exact chart0 values base hdet (survivor_is_pivot_chart0 values base hdet)

#print axioms
  Krenn.FrozenCase0NoncollapseType01Assembly.pivot_chart0_coordinate_name
#print axioms
  Krenn.FrozenCase0NoncollapseType01Assembly.refutes_noncollapse_slot_one_of_pivot_chart0

end Krenn.FrozenCase0NoncollapseType01Assembly
