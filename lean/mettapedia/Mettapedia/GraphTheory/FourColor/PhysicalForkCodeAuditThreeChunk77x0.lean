import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlatSplit

/-! Part 0 of page 77 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_77_c0 :
    pairsOk 3 (certCodes cert_three) ((certCodes cert_three).getD 77 leafF) 0 49 = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
