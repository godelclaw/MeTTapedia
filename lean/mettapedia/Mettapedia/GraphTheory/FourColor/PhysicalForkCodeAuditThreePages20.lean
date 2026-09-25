import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeCert

/-! Pages 80 to 83 of the audit at interface bound 3. -/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_80 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 80 leafF) = true := by
  decide +kernel

theorem page_three_81 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 81 leafF) = true := by
  decide +kernel

theorem page_three_82 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 82 leafF) = true := by
  decide +kernel

theorem page_three_83 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 83 leafF) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
