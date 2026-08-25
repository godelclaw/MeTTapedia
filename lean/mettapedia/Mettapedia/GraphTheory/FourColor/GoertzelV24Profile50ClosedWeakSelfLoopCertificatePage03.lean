import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50ClosedWeakSelfLoopCertificateData

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24Profile50ClosedWeakSelfLoopCertificate

open GoertzelV24FiniteTransitionWeakSelfLoop

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem valid_page_03 : witness.ValidPage transition 48 12 := by
  intro offset
  fin_cases offset <;> decide

end GoertzelV24Profile50ClosedWeakSelfLoopCertificate

end Mettapedia.GraphTheory.FourColor
