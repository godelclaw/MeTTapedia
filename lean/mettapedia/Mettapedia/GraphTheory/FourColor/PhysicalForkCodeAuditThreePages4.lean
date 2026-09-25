import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 16 to 19 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_16 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 16 leafF) = true := by
  decide +kernel

theorem page_three_17 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 17 leafF) = true := by
  decide +kernel

theorem page_three_18 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 18 leafF) = true := by
  decide +kernel

theorem page_three_19 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 19 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
