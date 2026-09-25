import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 40 to 43 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_40 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 40 leafF) = true := by
  decide +kernel

theorem page_three_41 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 41 leafF) = true := by
  decide +kernel

theorem page_three_42 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 42 leafF) = true := by
  decide +kernel

theorem page_three_43 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 43 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
