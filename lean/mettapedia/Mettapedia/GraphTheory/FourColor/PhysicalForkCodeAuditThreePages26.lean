import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 78 to 79 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_78 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 78 leafF) = true := by
  decide +kernel

theorem page_three_79 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 79 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
