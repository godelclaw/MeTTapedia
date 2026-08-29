import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCover

/-!
Top-down attachment of the B1 terminal cover to canonical chart-3 facts.
The terminal certificates previously carried several `w_34` zero facts as
leaf hypotheses; this wrapper derives those facts from source rows first.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalFromCanonical

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- The B1 terminal family is impossible using only its genuine split facts;
the downstream `w_34` zero facts are canonical consequences. -/
theorem refutes_chart3_b1_terminal_from_canonical
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 ≠ 0) (h34 : values 64 ≠ 0)
    (h05 : values 17 ≠ 0)
    (h12_12 : values 29 = 0) (h34_10 : values 63 = 0)
    (h05_02 : values 18 = 0) (h05_22 : values 24 = 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live
      values base hdet ⟨h23, h12, h13⟩ h24 h25
  have h13_12 : values 37 = 0 :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge.w13_12_zero_of_bothlive_sum_nonzero
      values base ⟨h23, h12, h13⟩ h13_10 hsum
  have h12_10 : values 27 = 0 :=
    (Krenn.FrozenCase0NoncollapseType01Chart3BothLive.chart3_surviving_coordinates
      values base hdet ⟨h23, h12, h13⟩).2.2
  obtain ⟨h34_12, h34_20, _h34_21, h34_22⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveBridge.w34_tail_zero_of_chart3_w12_10_w13_12_zero_w01_live
      values base ⟨h23, h12, h13⟩ h12_10 h13_12 h01
  exact
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCover.refutes_slot1_chart3_both_live_sum_nonzero_b1_terminal_cover
      values base hdet ⟨h23, h12, h13⟩ h24 h25 hsum h01 h34 h05 h12_10 h12_12
      h34_10 h34_12 h05_02 h05_22 h34_20 h34_22

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalFromCanonical.refutes_chart3_b1_terminal_from_canonical

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalFromCanonical
