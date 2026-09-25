import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 28 to 31 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_28 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 28 leafF) = true := by
  decide +kernel

theorem page_three_29 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 29 leafF) = true := by
  decide +kernel

theorem page_three_30 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 30 leafF) = true := by
  decide +kernel

theorem page_three_31 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 31 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
