import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 84 to 87 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_84 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 84 leafF) = true := by
  decide +kernel

theorem page_three_85 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 85 leafF) = true := by
  decide +kernel

theorem page_three_86 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 86 leafF) = true := by
  decide +kernel

theorem page_three_87 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 87 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
