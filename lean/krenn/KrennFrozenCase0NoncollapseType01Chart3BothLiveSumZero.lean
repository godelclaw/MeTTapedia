import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3SumzeroDirect
import KrennFrozenCase0NoncollapseType01Chart3W01ZeroW15W14LiveDirect
import KrennFrozenCase0NoncollapseType01Chart3W14ZeroW15Live
import KrennFrozenCase0NoncollapseType01Chart3W01LiveW15Zero
import KrennFrozenCase0NoncollapseType01Chart3B0Z0W14Nonzero
import KrennFrozenCase0NoncollapseType01Chart3B0Z1W14Zero
import KrennFrozenCase0NoncollapseType01Chart3B0NW15Nonzero
import KrennFrozenCase0NoncollapseType01Chart3B4W01Nonzero
import KrennFrozenCase0NoncollapseType01Chart3B4W01Zero
import KrennFrozenCase0NoncollapseType01Chart3B6
import KrennFrozenCase0NoncollapseType01Chart3B2Z
import KrennFrozenCase0NoncollapseType01Chart3B2N1W14Nonzero

/-!
The semantic cover for the zero-sum half of the surviving type-01 chart-3
branch.

This is deliberately an ordinary exhaustive `by_cases` proof, rather than a
claim inferred from the external branch manifest.  The individual terminal
theorems are either direct canonical contradictions or provenance-bound
strict certificate reflections.  Consequently every possible assignment of
the five remaining zero/nonzero coordinates reaches a named contradiction.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumZero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.FrozenCase0NoncollapseType01Chart3BothLive

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The both-pivots-live, zero-sum half of type-01 chart 3 has no common
zero.  This top-down split is independent of the discovery tree: the only
case distinction is on the five literal coordinates still free after the
canonical `w_12_10 = 0` consequence. -/
theorem refutes_chart3_both_live_sum_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0) : False := by
  obtain ⟨_, _, h12_10⟩ :=
    chart3_surviving_coordinates values base hdet chart
  by_cases h13_12 : values 37 = 0
  · by_cases h12_12 : values 29 = 0
    · by_cases h01 : values 1 = 0
      · by_cases h15 : values 45 = 0
        · by_cases h14 : values 42 = 0
          · exact Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.refutes_chart3_w01_w14_w15_zero
              values base chart h01 h14 h15
          · exact Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14Nonzero.refutes_chart3_b0z0_w14_nonzero values base hdet chart h24 h25 hsum
                h13_12 h12_12 h12_10 h01 h15 h14
        · by_cases h14 : values 42 = 0
          · exact Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14Zero.refutes_chart3_b0z1_w14_zero values base hdet chart h24 h25 hsum
                h13_12 h12_12 h12_10 h01 h15 h14
          · exact Krenn.FrozenCase0NoncollapseType01Chart3W01ZeroW15W14LiveDirect.refutes_chart3_w01_zero_w12_10_zero_w15_w14_live
                values base hdet chart h24 h25 h01 h12_10 h15 h14
      · by_cases h15 : values 45 = 0
        · exact Krenn.FrozenCase0NoncollapseType01Chart3W01LiveW15Zero.refutes_chart3_w01_live_w15_zero values base hdet chart h24 h25
              h13_12 h01 h15
        · exact Krenn.FrozenCase0NoncollapseType01Chart3B0NW15Nonzero.refutes_chart3_b0n_w15_nonzero values base hdet chart h24 h25 hsum
              h13_12 h12_12 h12_10 h01 h15
    · by_cases h01 : values 1 = 0
      · exact Krenn.FrozenCase0NoncollapseType01Chart3B2Z.refutes_chart3_b2_w01_zero values base hdet chart h24 h25 hsum
            h13_12 h12_12 h12_10 h01
      · by_cases h15 : values 45 = 0
        · exact Krenn.FrozenCase0NoncollapseType01Chart3W01LiveW15Zero.refutes_chart3_w01_live_w15_zero values base hdet chart h24 h25
              h13_12 h01 h15
        · by_cases h14 : values 42 = 0
          · exact Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroW15Live.refutes_w14_zero_w15_live_w12_12_live
                values base hdet chart h24 h25 h14 h15 h12_12
          · exact Krenn.FrozenCase0NoncollapseType01Chart3B2N1W14Nonzero.refutes_chart3_b2n1_w14_nonzero values base hdet chart h24 h25 hsum
                h13_12 h12_12 h12_10 h01 h15 h14
  · by_cases h12_12 : values 29 = 0
    · by_cases h01 : values 1 = 0
      · exact Krenn.FrozenCase0NoncollapseType01Chart3B4W01Zero.refutes_chart3_b4_w01_zero values base hdet chart h24 h25 hsum
            h13_12 h12_12 h12_10 h01
      · exact Krenn.FrozenCase0NoncollapseType01Chart3B4W01Nonzero.refutes_chart3_b4_w01_nonzero values base hdet chart h24 h25 hsum
            h13_12 h12_12 h12_10 h01
    · exact Krenn.FrozenCase0NoncollapseType01Chart3B6.refutes_chart3_b6 values base hdet chart h24 h25 hsum h13_12 h12_12 h12_10

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumZero.refutes_chart3_both_live_sum_zero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumZero
