import KrennFrozenCase0NoncollapseType01Chart3W23Nonzero
import KrennFrozenCase0NoncollapseType01Chart3W01Nonzero
import KrennFrozenCase0NoncollapseType01Chart3W03Nonzero
import KrennFrozenCase0NoncollapseType01Chart3W02Nonzero

/-!
The exhaustive closure of the pivot-chart-3 branch on which
`w_24_11 = 0` and `w_25_11 ≠ 0`.

The outer decisions and most reductions are direct consequences of the
canonical frozen equations.  Four terminal nonzero leaves are discharged
by strictly replayed exact certificates whose semantic bridges are imported
above.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3OnlyW25

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem refutes_slot1_chart3_only_w25
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 = 0) (h25 : values 56 ≠ 0) : False := by
  have h13_12 : values 37 = 0 :=
    w13_12_zero_of_w24_zero values base hdet chart h24 h25
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_w24_zero values base hdet chart h24 h25
  by_cases h14_11 : values 42 = 0
  · exact refutes_w24_zero_w13_10_zero_w14_11_zero
      values base hdet chart h24 h13_10 h14_11
  · obtain ⟨h03_00, h03_22⟩ :=
      w03_ends_zero_of_w14_11_nonzero
        values base hdet chart h24 h25 h13_12 h13_10 h14_11
    have h12_12 : values 29 = 0 :=
      w12_12_zero_of_w03_00_zero_w13_10_zero
        values base hdet h03_00 h13_10
    by_cases h23_22 : values 49 = 0
    · by_cases h01_11 : values 1 = 0
      · by_cases h03_11 : values 7 = 0
        · by_cases h02_11 : values 4 = 0
          · exact refutes_w02_11_zero
              values base hdet chart h01_11 h02_11 h03_11
          · obtain ⟨h15_11, h35_00, h35_22⟩ :=
              reductions_of_w02_11_nonzero
                values base hdet chart h24 h13_12 h13_10 h01_11
                  h14_11 h02_11
            exact
              Krenn.FrozenCase0NoncollapseType01Chart3W02Nonzero.refutes_slot1_chart3_w02_nonzero
                  values base hdet chart h24 h13_12 h13_10 h03_00 h03_22
                    h12_12 h23_22 h01_11 h03_11 h15_11 h35_00 h35_22
                    h25 h14_11 h02_11
        · obtain ⟨h25_10, h25_12, h25_20, h25_21, h25_22⟩ :=
            w25_offdiagonal_zero_of_w03_11_nonzero
              values base hdet chart h12_12 h01_11 h14_11 h03_11
          exact
            Krenn.FrozenCase0NoncollapseType01Chart3W03Nonzero.refutes_slot1_chart3_w03_nonzero
                values base hdet chart h24 h13_12 h13_10 h03_00 h03_22
                  h12_12 h23_22 h01_11 h25_10 h25_12 h25_20 h25_21
                  h25_22 h25 h14_11 h03_11
      · have h12 : values 28 = 0 := chart.2.1
        obtain ⟨h25_12, h25_20, h25_21, h25_22⟩ :=
          w25_tail_zero_of_w01_11_nonzero
            values base hdet h12 h12_12 h13_10 h01_11
        exact
          Krenn.FrozenCase0NoncollapseType01Chart3W01Nonzero.refutes_slot1_chart3_w01_nonzero
              values base hdet chart h24 h13_12 h13_10 h03_00 h03_22
                h12_12 h23_22 h25_12 h25_20 h25_21 h25_22
                h25 h14_11 h01_11
    · exact
        Krenn.FrozenCase0NoncollapseType01Chart3W23Nonzero.refutes_slot1_chart3_w23_nonzero
            values base hdet chart h24 h13_12 h13_10 h03_00 h03_22
              h12_12 h25 h14_11 h23_22

#print axioms refutes_slot1_chart3_only_w25

end Krenn.FrozenCase0NoncollapseType01Chart3OnlyW25
