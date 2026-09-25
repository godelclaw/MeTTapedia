import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 20 to 23 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_20 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 20 leafF) = true := by
  decide +kernel

theorem page_three_21 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 21 leafF) = true := by
  decide +kernel

theorem page_three_22 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 22 leafF) = true := by
  decide +kernel

theorem page_three_23 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 23 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
