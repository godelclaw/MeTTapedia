import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 36 to 39 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_36 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 36 leafF) = true := by
  decide +kernel

theorem page_three_37 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 37 leafF) = true := by
  decide +kernel

theorem page_three_38 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 38 leafF) = true := by
  decide +kernel

theorem page_three_39 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 39 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
