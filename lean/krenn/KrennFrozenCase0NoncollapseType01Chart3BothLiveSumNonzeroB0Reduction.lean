import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW01Live
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW12_12Live

/-!
The remaining semantic boundary of the nonzero-sum chart-3 branch.

The three returned literals are exactly the historical B0 coordinate pattern,
but this theorem is proved from the canonical chart facts and the named
closed faces.  It is a reduction, not a claim that B0 itself is closed.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- Any hypothetical witness on the nonzero-sum chart-3 branch lies on the
B0 literal face `(w_12_10, w_12_12, w_01_11) = (0, 0, 0)`. -/
theorem survivor_has_b0_literals
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0) :
    values 27 = 0 ∧ values 29 = 0 ∧ values 1 = 0 := by
  obtain ⟨_, _, h12_10⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLive.chart3_surviving_coordinates
      values base hdet chart
  refine ⟨h12_10, ?_, ?_⟩
  · by_cases h12_12 : values 29 = 0
    · exact h12_12
    · exact
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW12_12Live.refutes_chart3_both_live_sum_nonzero_w12_12_live
          values base hdet chart h24 h25 hsum h12_12).elim
  · by_cases h01 : values 1 = 0
    · exact h01
    · exact
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroW01Live.refutes_chart3_both_live_sum_nonzero_w01_live
          values base hdet chart h24 h25 hsum h01).elim

/-- In addition to the B0 split literals, the nonzero pivot sum forces the
remaining `w_13_12` coordinate used by the frozen B0 systems to vanish. -/
theorem survivor_has_b0_reductions
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0) :
    values 27 = 0 ∧ values 37 = 0 ∧ values 29 = 0 ∧ values 1 = 0 := by
  obtain ⟨h12_10, h12_12, h01⟩ :=
    survivor_has_b0_literals values base hdet chart h24 h25 hsum
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart h24 h25
  have h13_12 : values 37 = 0 :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge.w13_12_zero_of_bothlive_sum_nonzero
      values base chart h13_10 hsum
  exact ⟨h12_10, h13_12, h12_12, h01⟩

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_literals
#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction
