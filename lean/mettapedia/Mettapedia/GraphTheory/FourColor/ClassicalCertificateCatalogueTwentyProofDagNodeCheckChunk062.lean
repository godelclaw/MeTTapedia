import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock496_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 496 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock497_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 497 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock498_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 498 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock499_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 499 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock500_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 500 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock501_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 501 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock502_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 502 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock503_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 503 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 062. -/
theorem twentiethCatalogueProofDagNodeChunk062_checker
    (block : Nat) (hlower : 496 ≤ block) (hupper : block < 504) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock496_checker, twentiethCatalogueProofDagNodeBlock497_checker, twentiethCatalogueProofDagNodeBlock498_checker, twentiethCatalogueProofDagNodeBlock499_checker, twentiethCatalogueProofDagNodeBlock500_checker, twentiethCatalogueProofDagNodeBlock501_checker, twentiethCatalogueProofDagNodeBlock502_checker, twentiethCatalogueProofDagNodeBlock503_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
