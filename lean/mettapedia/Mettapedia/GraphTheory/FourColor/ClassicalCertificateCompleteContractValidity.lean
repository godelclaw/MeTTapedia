import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCompleteReductionMetadata
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateContractValidityCheck

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCompleteContractValidity

open ClassicalCertificateCompleteReductionMetadata
open ClassicalCertificateContractValidityCatalogue
open ClassicalCertificateContractValidityCatalogue.Catalogue
open ClassicalCertificateContractValidityCheck
open ClassicalCertificateContractValidityData
open ClassicalCertificateReductionMetadata
open ClassicalCertificateReductionMetadataData

/-- Every published classical configuration carries its exact original
construction provenance and a standard valid contract on the checked finite
hypermap. -/
theorem exists_validContract_classicalConfiguration
    (index : Nat) (hindex : index < 633) :
    ∃ configuration inverseCode metadata validityCertificate,
      ∃ certified : Certified configuration metadata,
      ClassicalCertificateCataloguePrograms.classicalConfigurationCatalogue.programAt?
          index = some configuration ∧
        ClassicalCertificateCatalogueHypermaps.classicalHypermapCatalogue.codeAt?
          index = some inverseCode ∧
        classicalReductionMetadataCatalogue.codeAt? index = some metadata ∧
        classicalContractValidityCatalogue.certificateAt? index =
          some validityCertificate ∧
        inverseCode.hypermap.Accepted ∧
        (ClassicalCertificateFacePartition.checkedHypermap
          certified.valid.partitionValid).ValidContract
          (ring metadata)
          (ClassicalCertificateContractValidity.selectedDarts metadata) := by
  obtain ⟨configuration, inverseCode, metadata,
      hconfiguration, hinverse, hmetadata, haccepted, hcertified⟩ :=
    exists_certified_classicalReductionMetadata index hindex
  obtain ⟨validityCertificate, hvalidityCertificate⟩ :=
    exists_certificate_of_populatedPrefixBoolean
      classicalContractValidityCatalogue 633
        classicalContractValidityCatalogue_populated index hindex
  refine ⟨configuration, inverseCode, metadata, validityCertificate, hcertified,
    hconfiguration, hinverse, hmetadata, hvalidityCertificate,
      haccepted, ?_⟩
  apply validContract_of_checker_true classicalReductionMetadataCatalogue
    classicalContractValidityCatalogue classicalContractValidity_checker
      index
  · simp only [valueBound, classicalContractValidityCatalogue_chunkCount,
      chunkSize]
    omega
  · exact hmetadata
  · exact hvalidityCertificate
  · exact hcertified.valid

end ClassicalCertificateCompleteContractValidity

end Mettapedia.GraphTheory.FourColor
