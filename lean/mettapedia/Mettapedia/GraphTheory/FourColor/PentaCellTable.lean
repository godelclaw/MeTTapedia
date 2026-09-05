import Mettapedia.GraphTheory.FourColor.PentaCellWords0
import Mettapedia.GraphTheory.FourColor.PentaCellWords1
import Mettapedia.GraphTheory.FourColor.PentaCellWords2
import Mettapedia.GraphTheory.FourColor.PentaCellWords3
import Mettapedia.GraphTheory.FourColor.PentaCellWords4
import Mettapedia.GraphTheory.FourColor.PentaCellWords5
import Mettapedia.GraphTheory.FourColor.PentaCellWords6
import Mettapedia.GraphTheory.FourColor.PentaCellWords7
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! The table of `PentaCell` equals the literal, and the corridor stabilises at index 4. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.PentaCell

open Presented Pres

theorem all_words : ∀ X, X < 729 → P.enumMask X = labTable[X]! := by
  intro X hX
  by_cases c0 : X < 92
  · exact W0.chunk X c0
  by_cases c1 : X < 184
  · exact W1.chunk X (by omega) c1
  by_cases c2 : X < 276
  · exact W2.chunk X (by omega) c2
  by_cases c3 : X < 368
  · exact W3.chunk X (by omega) c3
  by_cases c4 : X < 460
  · exact W4.chunk X (by omega) c4
  by_cases c5 : X < 552
  · exact W5.chunk X (by omega) c5
  by_cases c6 : X < 644
  · exact W6.chunk X (by omega) c6
  exact W7.chunk X (by omega) hX

set_option maxRecDepth 100000 in
theorem table_eq : P.table = labTable :=
  table_eq_of_forall P labTable (by decide +kernel) all_words

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range0 : stabilizesRangeAt 4 0 92 labTable = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range1 : stabilizesRangeAt 4 92 92 labTable = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range2 : stabilizesRangeAt 4 184 92 labTable = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range3 : stabilizesRangeAt 4 276 92 labTable = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range4 : stabilizesRangeAt 4 368 92 labTable = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range5 : stabilizesRangeAt 4 460 92 labTable = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range6 : stabilizesRangeAt 4 552 92 labTable = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem range7 : stabilizesRangeAt 4 644 92 labTable = true := by decide +kernel

theorem stabilizes : stabilizesAt 4 729 P.table = true := by
  rw [table_eq]
  apply stabilizesAt_of_ranges 4 729 92 labTable (by norm_num)
  intro c hc
  have : c < 8 := by omega
  interval_cases c
  · exact range0
  · exact range1
  · exact range2
  · exact range3
  · exact range4
  · exact range5
  · exact range6
  · exact range7

end Mettapedia.GraphTheory.FourColor.TubeSlab.PentaCell
