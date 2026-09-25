import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 10 to 11 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_10 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 10 leafF) = true := by
  decide +kernel

theorem page_three_11 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 11 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
