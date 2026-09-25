import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 4 to 7 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_4 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 4 leafF) = true := by
  decide +kernel

theorem page_three_5 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 5 leafF) = true := by
  decide +kernel

theorem page_three_6 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 6 leafF) = true := by
  decide +kernel

theorem page_three_7 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 7 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
