import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock304_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 304 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock305_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 305 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock306_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 306 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock307_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 307 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock308_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 308 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock309_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 309 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock310_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 310 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock311_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 311 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 038. -/
theorem twentiethCatalogueProofDagNodeChunk038_checker
    (block : Nat) (hlower : 304 ≤ block) (hupper : block < 312) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock304_checker, twentiethCatalogueProofDagNodeBlock305_checker, twentiethCatalogueProofDagNodeBlock306_checker, twentiethCatalogueProofDagNodeBlock307_checker, twentiethCatalogueProofDagNodeBlock308_checker, twentiethCatalogueProofDagNodeBlock309_checker, twentiethCatalogueProofDagNodeBlock310_checker, twentiethCatalogueProofDagNodeBlock311_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
