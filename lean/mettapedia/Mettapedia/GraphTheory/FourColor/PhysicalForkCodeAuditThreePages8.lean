import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 32 to 35 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_32 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 32 leafF) = true := by
  decide +kernel

theorem page_three_33 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 33 leafF) = true := by
  decide +kernel

theorem page_three_34 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 34 leafF) = true := by
  decide +kernel

theorem page_three_35 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 35 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
