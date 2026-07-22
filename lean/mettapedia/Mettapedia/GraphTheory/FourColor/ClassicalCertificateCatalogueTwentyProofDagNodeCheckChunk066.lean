import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock528_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 528 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock529_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 529 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock530_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 530 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock531_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 531 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock532_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 532 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock533_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 533 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock534_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 534 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock535_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 535 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 066. -/
theorem twentiethCatalogueProofDagNodeChunk066_checker
    (block : Nat) (hlower : 528 ≤ block) (hupper : block < 536) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock528_checker, twentiethCatalogueProofDagNodeBlock529_checker, twentiethCatalogueProofDagNodeBlock530_checker, twentiethCatalogueProofDagNodeBlock531_checker, twentiethCatalogueProofDagNodeBlock532_checker, twentiethCatalogueProofDagNodeBlock533_checker, twentiethCatalogueProofDagNodeBlock534_checker, twentiethCatalogueProofDagNodeBlock535_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
