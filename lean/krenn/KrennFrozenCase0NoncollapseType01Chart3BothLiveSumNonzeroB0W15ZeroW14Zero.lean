import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction
import KrennFrozenCase0NoncollapseType01Chart3SumzeroDirect

/-!
The first structural child of the remaining B0 nonzero-sum face.

The external B0 tree split further on `w_34_11`, then on `w_15_11` and
`w_14_11`.  This leaf needs no certificate: canonical amplitude row 745 is
already contradictory once `w_01_11`, `w_14_11`, and `w_15_11` vanish.
The B0 reduction supplies the first of those equalities.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14Zero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- The B0 subface `w_15_11 = w_14_11 = 0` is impossible.  This is stronger
than the corresponding live-`w_34_11` external child, whose additional
nonvanishing assumption is not needed. -/
theorem refutes_chart3_both_live_sum_nonzero_b0_w15_zero_w14_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 = 0) (h14 : values 42 = 0) :
    False := by
  obtain ⟨_, _, _, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  exact
    Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.refutes_chart3_w01_w14_w15_zero
      values base chart h01 h14 h15

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14Zero.refutes_chart3_both_live_sum_nonzero_b0_w15_zero_w14_zero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14Zero
