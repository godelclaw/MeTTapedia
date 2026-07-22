import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock552_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 552 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock553_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 553 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock554_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 554 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock555_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 555 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock556_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 556 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock557_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 557 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock558_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 558 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock559_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 559 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 069. -/
theorem twentiethCatalogueProofDagNodeChunk069_checker
    (block : Nat) (hlower : 552 ≤ block) (hupper : block < 560) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock552_checker, twentiethCatalogueProofDagNodeBlock553_checker, twentiethCatalogueProofDagNodeBlock554_checker, twentiethCatalogueProofDagNodeBlock555_checker, twentiethCatalogueProofDagNodeBlock556_checker, twentiethCatalogueProofDagNodeBlock557_checker, twentiethCatalogueProofDagNodeBlock558_checker, twentiethCatalogueProofDagNodeBlock559_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
