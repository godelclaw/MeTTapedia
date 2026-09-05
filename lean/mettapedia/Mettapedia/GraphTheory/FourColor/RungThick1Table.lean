import Mettapedia.GraphTheory.FourColor.RungThick1Words0
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! The table of `RungThick1` equals the literal, and the corridor stabilises at index 6. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick1

open Presented Pres

theorem all_words : ∀ X, X < 27 → P.enumMask X = labTable[X]! := by
  intro X hX
  exact W0.chunk X hX

theorem table_eq : P.table = labTable :=
  table_eq_of_forall P labTable (by decide) all_words

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range0 : stabilizesRangeAtPeriod 6 3 0 92 labTable = true := by decide +kernel

theorem stabilizes : stabilizesAtPeriod 6 3 27 P.table = true := by
  rw [table_eq]
  apply stabilizesAtPeriod_of_ranges 6 3 27 92 labTable (by norm_num)
  intro c hc
  have : c < 1 := by omega
  interval_cases c
  · exact range0

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick1
