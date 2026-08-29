import KrennFrozenCase0NoncollapseType01Chart1Diagzero
import KrennFrozenCase0NoncollapseType01Chart1Sumzero
import KrennFrozenCase0NoncollapseType01Chart1X24NonzeroX25Zero

/-!
Kernel assembly for pivot chart 1 of physical non-collapse type 01.

The proof splits first on the two surviving diagonal pivots.  When both are
nonzero, it splits on their sum.  The zero-sum branch is already refuted by
the reflected strict certificate tree; otherwise a canonical amplitude row
forces equality of the secondary coefficients, and the four-leaf diagonal
certificate assembly refutes that branch.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart1

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot

/-- Pivot chart 1 of physical non-collapse type 01 is impossible. -/
theorem refutes_slot1_pivot_chart1
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values) : False := by
  by_cases h24 : values 51 = 0
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart1X24Zero.refutes_slot1_chart1_w24_zero
        values base hdet chart h24
  · by_cases h25 : values 56 = 0
    · exact
        Krenn.FrozenCase0NoncollapseType01Chart1X24NonzeroX25Zero.refutes_slot1_chart1_w24_nonzero_w25_zero
          values base hdet chart h24 h25
    · by_cases hsum : values 51 + values 56 = 0
      · exact
          Krenn.FrozenCase0NoncollapseType01Chart1Sumzero.refutes_slot1_chart1_sumzero
            values base hdet chart h24 h25 hsum
      · have heq : values 31 = values 39 :=
          (Krenn.FrozenCase0NoncollapseType01Chart1X24Zero.chart1_pivot_sum_or_equal
            values base hdet chart).resolve_left hsum
        exact
          Krenn.FrozenCase0NoncollapseType01Chart1Diagzero.refutes_equal_secondary
            values base hdet chart h24 h25 hsum heq

#print axioms refutes_slot1_pivot_chart1

end Krenn.FrozenCase0NoncollapseType01Chart1
