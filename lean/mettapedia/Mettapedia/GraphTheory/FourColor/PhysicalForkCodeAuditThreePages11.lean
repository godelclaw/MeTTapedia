import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 44 to 47 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_44 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 44 leafF) = true := by
  decide +kernel

theorem page_three_45 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 45 leafF) = true := by
  decide +kernel

theorem page_three_46 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 46 leafF) = true := by
  decide +kernel

theorem page_three_47 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 47 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
