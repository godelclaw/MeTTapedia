import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataCheck
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLinkCheck

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCompleteReductionMetadata

open ClassicalCertificateConfigurationProvenance
open ClassicalCertificateReductionMetadata
open ClassicalCertificateReductionMetadataCheck
open ClassicalCertificateReductionMetadataLink
open ClassicalCertificateReductionMetadataLinkCheck

/-- Every published classical configuration has an accepted exported
hypermap and a complete, locally valid reduction record exactly linked to its
original construction program, canonical boundary, and selected contract. -/
theorem exists_certified_classicalReductionMetadata
    (index : Nat) (hindex : index < 633) :
    ∃ configuration inverseCode code,
      ClassicalCertificateCataloguePrograms.classicalConfigurationCatalogue.programAt?
          index = some configuration ∧
        ClassicalCertificateCatalogueHypermaps.classicalHypermapCatalogue.codeAt?
          index = some inverseCode ∧
        ClassicalCertificateReductionMetadataData.classicalReductionMetadataCatalogue.codeAt?
          index = some code ∧
        inverseCode.hypermap.Accepted ∧
        Certified configuration code := by
  obtain ⟨configuration, inverseCode, hconfiguration, hinverse,
      hmaterialized, haccepted⟩ :=
    exists_accepted_materialized_classicalConfiguration index hindex
  obtain ⟨code, hcode, hvalid⟩ :=
    exists_valid_classicalReductionMetadata index hindex
  have hentry := classicalReductionMetadataLinkEntry_checker index hindex
  have hconditions := conditions_of_entryBoolean_true index hentry
    configuration hconfiguration inverseCode hinverse code hcode
  refine ⟨configuration, inverseCode, code, hconfiguration, hinverse,
    hcode, haccepted, hvalid, ?_⟩
  exact programLink_of_conditions configuration inverseCode code
    hmaterialized hconditions

end ClassicalCertificateCompleteReductionMetadata

end Mettapedia.GraphTheory.FourColor
