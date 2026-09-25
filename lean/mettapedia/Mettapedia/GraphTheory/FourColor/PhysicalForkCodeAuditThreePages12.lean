import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 48 to 51 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_48 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 48 leafF) = true := by
  decide +kernel

theorem page_three_49 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 49 leafF) = true := by
  decide +kernel

theorem page_three_50 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 50 leafF) = true := by
  decide +kernel

theorem page_three_51 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 51 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
