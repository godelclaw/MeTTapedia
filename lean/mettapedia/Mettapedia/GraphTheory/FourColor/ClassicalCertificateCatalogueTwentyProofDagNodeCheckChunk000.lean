import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock000_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 0 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock001_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 1 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock002_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 2 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock003_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 3 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock004_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 4 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock005_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 5 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock006_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 6 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock007_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 7 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 000. -/
theorem twentiethCatalogueProofDagNodeChunk000_checker
    (block : Nat) (hlower : 0 ≤ block) (hupper : block < 8) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock000_checker,
      twentiethCatalogueProofDagNodeBlock001_checker,
      twentiethCatalogueProofDagNodeBlock002_checker,
      twentiethCatalogueProofDagNodeBlock003_checker,
      twentiethCatalogueProofDagNodeBlock004_checker,
      twentiethCatalogueProofDagNodeBlock005_checker,
      twentiethCatalogueProofDagNodeBlock006_checker,
      twentiethCatalogueProofDagNodeBlock007_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
