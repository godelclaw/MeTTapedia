import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 24 to 27 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_24 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 24 leafF) = true := by
  decide +kernel

theorem page_three_25 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 25 leafF) = true := by
  decide +kernel

theorem page_three_26 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 26 leafF) = true := by
  decide +kernel

theorem page_three_27 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 27 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
