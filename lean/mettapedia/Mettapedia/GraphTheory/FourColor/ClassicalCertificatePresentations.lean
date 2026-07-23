import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationData5
import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationData6
import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationData7
import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationData8
import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationData9
import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationData10
import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationData11

/-! # Structurally checked finite unavoidability presentations -/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentations

open ClassicalCertificatePresentationCertificate

/-- All seven finite presentation trees pass the same reflected split and
similarity checker. -/
theorem all_structureChecks :
    structureCheck ClassicalCertificatePresentationData5.arity
        ClassicalCertificatePresentationData5.code = true ∧
    structureCheck ClassicalCertificatePresentationData6.arity
        ClassicalCertificatePresentationData6.code = true ∧
    structureCheck ClassicalCertificatePresentationData7.arity
        ClassicalCertificatePresentationData7.code = true ∧
    structureCheck ClassicalCertificatePresentationData8.arity
        ClassicalCertificatePresentationData8.code = true ∧
    structureCheck ClassicalCertificatePresentationData9.arity
        ClassicalCertificatePresentationData9.code = true ∧
    structureCheck ClassicalCertificatePresentationData10.arity
        ClassicalCertificatePresentationData10.code = true ∧
    structureCheck ClassicalCertificatePresentationData11.arity
        ClassicalCertificatePresentationData11.code = true := by
  exact ⟨ClassicalCertificatePresentationData5.structureCheck_eq_true,
    ClassicalCertificatePresentationData6.structureCheck_eq_true,
    ClassicalCertificatePresentationData7.structureCheck_eq_true,
    ClassicalCertificatePresentationData8.structureCheck_eq_true,
    ClassicalCertificatePresentationData9.structureCheck_eq_true,
    ClassicalCertificatePresentationData10.structureCheck_eq_true,
    ClassicalCertificatePresentationData11.structureCheck_eq_true⟩

#print axioms all_structureChecks

end ClassicalCertificatePresentations

end Mettapedia.GraphTheory.FourColor
