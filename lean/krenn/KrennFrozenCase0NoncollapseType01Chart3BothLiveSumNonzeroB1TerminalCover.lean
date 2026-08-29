import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalB4Bridge

/-!
The exhaustive `w_34_00` cover at the B1 terminal interface.

The zero branch is the original terminal certificate.  The nonzero branch is
the B4 monomial-closure certificate.  Keeping this dichotomy here makes the
parent branch explicit rather than relying on a human reading two leaf names.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCover

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- Under the B1 terminal hypotheses, both possibilities for `w_34_00` are
impossible. -/
theorem refutes_slot1_chart3_both_live_sum_nonzero_b1_terminal_cover
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 ≠ 0) (h34 : values 64 ≠ 0) (h05 : values 17 ≠ 0)
    (h12_10 : values 27 = 0) (h12_12 : values 29 = 0)
    (h34_10 : values 63 = 0) (h34_12 : values 65 = 0)
    (h05_02 : values 18 = 0) (h05_22 : values 24 = 0)
    (h34_20 : values 66 = 0) (h34_22 : values 68 = 0) : False := by
  by_cases h34_00 : values 61 = 0
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge.refutes_slot1_chart3_both_live_sum_nonzero_b1_terminal
        values base hdet chart h24 h25 hsum h01 h34 h05 h05_02 h05_22 h34_00
        h34_10 h34_12 h34_20 h34_22
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalB4Bridge.refutes_slot1_chart3_both_live_sum_nonzero_b1_terminal_b4
        values base hdet chart h24 h25 hsum h01 h34 h05 h34_00 h12_10 h12_12
        h34_10 h34_12 h05_02 h05_22 h34_20 h34_22

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCover.refutes_slot1_chart3_both_live_sum_nonzero_b1_terminal_cover

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCover
