import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock640_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 640 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock641_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 641 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock642_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 642 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock643_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 643 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock644_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 644 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock645_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 645 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock646_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 646 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock647_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 647 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 080. -/
theorem twentiethCatalogueProofDagNodeChunk080_checker
    (block : Nat) (hlower : 640 ≤ block) (hupper : block < 648) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock640_checker, twentiethCatalogueProofDagNodeBlock641_checker, twentiethCatalogueProofDagNodeBlock642_checker, twentiethCatalogueProofDagNodeBlock643_checker, twentiethCatalogueProofDagNodeBlock644_checker, twentiethCatalogueProofDagNodeBlock645_checker, twentiethCatalogueProofDagNodeBlock646_checker, twentiethCatalogueProofDagNodeBlock647_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
