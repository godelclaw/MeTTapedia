import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mettapedia.GraphTheory.FourColor.GoertzelV24Profile50AnnularWeakSelfLoopCertificateData

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24Profile50AnnularWeakSelfLoopCertificate

open GoertzelV24FiniteTransitionWeakSelfLoop

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem valid_page_12 : witness.ValidPage transition 192 16 := by
  intro offset
  fin_cases offset <;> decide

end GoertzelV24Profile50AnnularWeakSelfLoopCertificate

end Mettapedia.GraphTheory.FourColor
