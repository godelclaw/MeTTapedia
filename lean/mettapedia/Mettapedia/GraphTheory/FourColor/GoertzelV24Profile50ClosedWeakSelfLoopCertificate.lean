import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50ClosedWeakSelfLoopCertificatePage00
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50ClosedWeakSelfLoopCertificatePage01
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50ClosedWeakSelfLoopCertificatePage02
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50ClosedWeakSelfLoopCertificatePage03

/-!
# Checked weak L2 for one measured source two-pair transition

The `closed` `(5,0)` payload has 60 states.  Its source JSON
fingerprint is `3690cb214cfb56a6`.  The theorem concerns exactly this decoded
finite transition; identifying it with every source-legal corridor remains a
separate fidelity theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24Profile50ClosedWeakSelfLoopCertificate

open GoertzelV24FiniteTransitionWeakSelfLoop

theorem all_pages_valid : witness.ValidPage transition 0 60 := by
  have joined_01 := valid_page_00.append valid_page_01
  have joined_02 := joined_01.append valid_page_02
  have joined_03 := joined_02.append valid_page_03
  simpa using joined_03

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

end GoertzelV24Profile50ClosedWeakSelfLoopCertificate

end Mettapedia.GraphTheory.FourColor
