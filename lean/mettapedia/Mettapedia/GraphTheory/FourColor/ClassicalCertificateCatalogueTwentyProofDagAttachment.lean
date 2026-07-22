import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataCheckBlock004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataData

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagAttachment

open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction
open ClassicalCertificateReductionMetadata
open ClassicalCertificateReductionMetadataCatalogue
open ClassicalCertificateReductionMetadataCheck
open ClassicalCertificateReductionMetadataData

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- The complete reduction record at classical catalogue index nineteen. -/
def twentiethCatalogueReductionMetadata :
    ClassicalCertificateReductionMetadata.Code :=
  classicalReductionMetadataChunk01[3]'(by decide)

theorem twentiethCatalogueReductionMetadata_lookup :
    classicalReductionMetadataCatalogue.codeAt? 19 =
      some twentiethCatalogueReductionMetadata := by
  rfl

theorem twentiethCatalogueReductionMetadata_checker :
    ClassicalCertificateReductionMetadata.checker
      twentiethCatalogueReductionMetadata = true := by
  have hblock := classicalReductionMetadataBlock004_checker
  have hentry := (List.all_eq_true.1 hblock) 3 (by decide)
  have hlookup : classicalReductionMetadataChunk01[3]? =
      some twentiethCatalogueReductionMetadata := by
    rfl
  simpa [Certificate.localBlockBoolean, hlookup] using hentry

/-- Semantic validity of the exact reduction record used by the proof DAG. -/
def twentiethCatalogueReductionMetadataValid :
    ClassicalCertificateReductionMetadata.Valid
      twentiethCatalogueReductionMetadata :=
  ClassicalCertificateReductionMetadata.valid_of_checker_true
    twentiethCatalogueReductionMetadata
      twentiethCatalogueReductionMetadata_checker

end ClassicalCertificateCatalogueTwentyProofDagAttachment

end Mettapedia.GraphTheory.FourColor
