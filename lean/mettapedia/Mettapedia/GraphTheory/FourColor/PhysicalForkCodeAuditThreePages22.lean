import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 88 to 91 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_88 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 88 leafF) = true := by
  decide +kernel

theorem page_three_89 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 89 leafF) = true := by
  decide +kernel

theorem page_three_90 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 90 leafF) = true := by
  decide +kernel

theorem page_three_91 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 91 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
