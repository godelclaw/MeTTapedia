import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 60 to 63 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_60 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 60 leafF) = true := by
  decide +kernel

theorem page_three_61 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 61 leafF) = true := by
  decide +kernel

theorem page_three_62 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 62 leafF) = true := by
  decide +kernel

theorem page_three_63 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 63 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
