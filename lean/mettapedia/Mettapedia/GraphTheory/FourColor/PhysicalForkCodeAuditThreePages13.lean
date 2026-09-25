import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 52 to 55 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_52 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 52 leafF) = true := by
  decide +kernel

theorem page_three_53 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 53 leafF) = true := by
  decide +kernel

theorem page_three_54 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 54 leafF) = true := by
  decide +kernel

theorem page_three_55 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 55 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
