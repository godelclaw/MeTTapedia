import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock568_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 568 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock569_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 569 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock570_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 570 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock571_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 571 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock572_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 572 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock573_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 573 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock574_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 574 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock575_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 575 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 071. -/
theorem twentiethCatalogueProofDagNodeChunk071_checker
    (block : Nat) (hlower : 568 ≤ block) (hupper : block < 576) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock568_checker, twentiethCatalogueProofDagNodeBlock569_checker, twentiethCatalogueProofDagNodeBlock570_checker, twentiethCatalogueProofDagNodeBlock571_checker, twentiethCatalogueProofDagNodeBlock572_checker, twentiethCatalogueProofDagNodeBlock573_checker, twentiethCatalogueProofDagNodeBlock574_checker, twentiethCatalogueProofDagNodeBlock575_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
