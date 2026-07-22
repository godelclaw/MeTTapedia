import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock392_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 392 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock393_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 393 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock394_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 394 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock395_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 395 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock396_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 396 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock397_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 397 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock398_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 398 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock399_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 399 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 049. -/
theorem twentiethCatalogueProofDagNodeChunk049_checker
    (block : Nat) (hlower : 392 ≤ block) (hupper : block < 400) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock392_checker, twentiethCatalogueProofDagNodeBlock393_checker, twentiethCatalogueProofDagNodeBlock394_checker, twentiethCatalogueProofDagNodeBlock395_checker, twentiethCatalogueProofDagNodeBlock396_checker, twentiethCatalogueProofDagNodeBlock397_checker, twentiethCatalogueProofDagNodeBlock398_checker, twentiethCatalogueProofDagNodeBlock399_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
