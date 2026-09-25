import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 0 to 3 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_0 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 0 leafF) = true := by
  decide +kernel

theorem page_three_1 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 1 leafF) = true := by
  decide +kernel

theorem page_three_2 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 2 leafF) = true := by
  decide +kernel

theorem page_three_3 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 3 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
