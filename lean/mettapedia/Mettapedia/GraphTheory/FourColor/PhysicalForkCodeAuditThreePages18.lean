import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 72 to 75 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_72 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 72 leafF) = true := by
  decide +kernel

theorem page_three_73 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 73 leafF) = true := by
  decide +kernel

theorem page_three_74 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 74 leafF) = true := by
  decide +kernel

theorem page_three_75 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 75 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
