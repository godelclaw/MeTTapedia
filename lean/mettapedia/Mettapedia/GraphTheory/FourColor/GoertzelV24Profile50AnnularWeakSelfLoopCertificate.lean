import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage00
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage01
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage02
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage03
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage04
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage05
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage06
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage07
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage08
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage09
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage10
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage11
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage12
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage13
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage14
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage15
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage16
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage17
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage18
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage19
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage20
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage21
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage22
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage23
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage24
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage25
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage26
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage27
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificatePage28

/-!
# Checked weak L2 for one measured source two-pair transition

The `annular` `(5,0)` payload has 455 states.  Its source JSON
fingerprint is `66df6f15e49b595e`.  The theorem concerns exactly this decoded
finite transition; identifying it with every source-legal corridor remains a
separate fidelity theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24Profile50AnnularWeakSelfLoopCertificate

open GoertzelV24FiniteTransitionWeakSelfLoop

theorem all_pages_valid : witness.ValidPage transition 0 455 := by
  have joined_01 := valid_page_00.append valid_page_01
  have joined_02 := joined_01.append valid_page_02
  have joined_03 := joined_02.append valid_page_03
  have joined_04 := joined_03.append valid_page_04
  have joined_05 := joined_04.append valid_page_05
  have joined_06 := joined_05.append valid_page_06
  have joined_07 := joined_06.append valid_page_07
  have joined_08 := joined_07.append valid_page_08
  have joined_09 := joined_08.append valid_page_09
  have joined_10 := joined_09.append valid_page_10
  have joined_11 := joined_10.append valid_page_11
  have joined_12 := joined_11.append valid_page_12
  have joined_13 := joined_12.append valid_page_13
  have joined_14 := joined_13.append valid_page_14
  have joined_15 := joined_14.append valid_page_15
  have joined_16 := joined_15.append valid_page_16
  have joined_17 := joined_16.append valid_page_17
  have joined_18 := joined_17.append valid_page_18
  have joined_19 := joined_18.append valid_page_19
  have joined_20 := joined_19.append valid_page_20
  have joined_21 := joined_20.append valid_page_21
  have joined_22 := joined_21.append valid_page_22
  have joined_23 := joined_22.append valid_page_23
  have joined_24 := joined_23.append valid_page_24
  have joined_25 := joined_24.append valid_page_25
  have joined_26 := joined_25.append valid_page_26
  have joined_27 := joined_26.append valid_page_27
  have joined_28 := joined_27.append valid_page_28
  simpa using joined_28

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem witness_valid : witness.Valid transition := by
  exact witness.valid_of_page_zero transition (by decide) (by decide)
    (by decide) (by decide) (by decide) all_pages_valid

/-- Every state in this measured transition reaches a self-loop in at most two
one-ring steps. -/
theorem all_states_reach_selfLoop_within_two
    (source : Fin transition.stateCount) :
    ReachesSelfLoopWithinTwo transition source.val :=
  witness.all_reach_selfLoop_within_two transition witness_valid source

end GoertzelV24Profile50AnnularWeakSelfLoopCertificate

end Mettapedia.GraphTheory.FourColor
