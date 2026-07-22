import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock424_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 424 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock425_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 425 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock426_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 426 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock427_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 427 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock428_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 428 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock429_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 429 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock430_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 430 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock431_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 431 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 053. -/
theorem twentiethCatalogueProofDagNodeChunk053_checker
    (block : Nat) (hlower : 424 ≤ block) (hupper : block < 432) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock424_checker, twentiethCatalogueProofDagNodeBlock425_checker, twentiethCatalogueProofDagNodeBlock426_checker, twentiethCatalogueProofDagNodeBlock427_checker, twentiethCatalogueProofDagNodeBlock428_checker, twentiethCatalogueProofDagNodeBlock429_checker, twentiethCatalogueProofDagNodeBlock430_checker, twentiethCatalogueProofDagNodeBlock431_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
