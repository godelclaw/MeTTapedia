import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationHubcapCover
import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentations

/-! # Checked linear covers for all finite-presentation hubcaps -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationHubcapCoverage

open ClassicalCertificatePresentationHubcapCover

/-- The arity-five presentation has valid linear hubcap covers. -/
theorem hubcapCoverCheck5 :
    allHubcapsCover ClassicalCertificatePresentationData5.arity
      ClassicalCertificatePresentationData5.code = true := by
  rfl

/-- The arity-six presentation has valid linear hubcap covers. -/
theorem hubcapCoverCheck6 :
    allHubcapsCover ClassicalCertificatePresentationData6.arity
      ClassicalCertificatePresentationData6.code = true := by
  rfl

/-- The arity-seven presentation has valid linear hubcap covers. -/
theorem hubcapCoverCheck7 :
    allHubcapsCover ClassicalCertificatePresentationData7.arity
      ClassicalCertificatePresentationData7.code = true := by
  rfl

/-- The arity-eight presentation has valid linear hubcap covers. -/
theorem hubcapCoverCheck8 :
    allHubcapsCover ClassicalCertificatePresentationData8.arity
      ClassicalCertificatePresentationData8.code = true := by
  rfl

/-- The arity-nine presentation has valid linear hubcap covers. -/
theorem hubcapCoverCheck9 :
    allHubcapsCover ClassicalCertificatePresentationData9.arity
      ClassicalCertificatePresentationData9.code = true := by
  rfl

/-- The arity-ten presentation has valid linear hubcap covers. -/
theorem hubcapCoverCheck10 :
    allHubcapsCover ClassicalCertificatePresentationData10.arity
      ClassicalCertificatePresentationData10.code = true := by
  rfl

/-- The arity-eleven presentation has valid linear hubcap covers. -/
theorem hubcapCoverCheck11 :
    allHubcapsCover ClassicalCertificatePresentationData11.arity
      ClassicalCertificatePresentationData11.code = true := by
  rfl

/-- Every hubcap in each of the seven finite presentations has a valid
coefficient-two linear cover and closes its arity-dependent strict bound. -/
theorem all_hubcapCoverChecks :
    allHubcapsCover ClassicalCertificatePresentationData5.arity
        ClassicalCertificatePresentationData5.code = true ∧
    allHubcapsCover ClassicalCertificatePresentationData6.arity
        ClassicalCertificatePresentationData6.code = true ∧
    allHubcapsCover ClassicalCertificatePresentationData7.arity
        ClassicalCertificatePresentationData7.code = true ∧
    allHubcapsCover ClassicalCertificatePresentationData8.arity
        ClassicalCertificatePresentationData8.code = true ∧
    allHubcapsCover ClassicalCertificatePresentationData9.arity
        ClassicalCertificatePresentationData9.code = true ∧
    allHubcapsCover ClassicalCertificatePresentationData10.arity
        ClassicalCertificatePresentationData10.code = true ∧
    allHubcapsCover ClassicalCertificatePresentationData11.arity
        ClassicalCertificatePresentationData11.code = true := by
  exact ⟨hubcapCoverCheck5, hubcapCoverCheck6, hubcapCoverCheck7,
    hubcapCoverCheck8, hubcapCoverCheck9, hubcapCoverCheck10,
    hubcapCoverCheck11⟩

#print axioms all_hubcapCoverChecks

end ClassicalCertificatePresentationHubcapCoverage

end Mettapedia.GraphTheory.FourColor
