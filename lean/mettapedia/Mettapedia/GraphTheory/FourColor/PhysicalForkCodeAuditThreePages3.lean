import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 12 to 15 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_12 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 12 leafF) = true := by
  decide +kernel

theorem page_three_13 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 13 leafF) = true := by
  decide +kernel

theorem page_three_14 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 14 leafF) = true := by
  decide +kernel

theorem page_three_15 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 15 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
