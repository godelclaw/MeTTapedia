import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 64 to 67 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_64 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 64 leafF) = true := by
  decide +kernel

theorem page_three_65 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 65 leafF) = true := by
  decide +kernel

theorem page_three_66 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 66 leafF) = true := by
  decide +kernel

theorem page_three_67 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 67 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
