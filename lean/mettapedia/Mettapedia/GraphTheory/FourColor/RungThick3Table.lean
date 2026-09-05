import Mettapedia.GraphTheory.FourColor.RungThick3Words0
import Mettapedia.GraphTheory.FourColor.RungThick3Words1
import Mettapedia.GraphTheory.FourColor.RungThick3Words2
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! The table of `RungThick3` equals the literal, and the corridor stabilises at index 10. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick3

open Presented Pres

theorem all_words : ∀ X, X < 243 → P.enumMask X = labTable[X]! := by
  intro X hX
  by_cases c0 : X < 92
  · exact W0.chunk X c0
  by_cases c1 : X < 184
  · exact W1.chunk X (by omega) c1
  exact W2.chunk X (by omega) hX

set_option maxRecDepth 100000 in
theorem table_eq : P.table = labTable :=
  table_eq_of_forall P labTable (by decide +kernel) all_words

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range0 : stabilizesRangeAt 10 0 92 labTable = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range1 : stabilizesRangeAt 10 92 92 labTable = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range2 : stabilizesRangeAt 10 184 92 labTable = true := by decide +kernel

theorem stabilizes : stabilizesAt 10 243 P.table = true := by
  rw [table_eq]
  apply stabilizesAt_of_ranges 10 243 92 labTable (by norm_num)
  intro c hc
  have : c < 3 := by omega
  interval_cases c
  · exact range0
  · exact range1
  · exact range2

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick3
