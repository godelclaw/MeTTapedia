import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock592_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 592 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock593_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 593 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock594_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 594 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock595_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 595 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock596_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 596 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock597_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 597 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock598_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 598 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock599_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 599 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 074. -/
theorem twentiethCatalogueProofDagNodeChunk074_checker
    (block : Nat) (hlower : 592 ≤ block) (hupper : block < 600) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock592_checker, twentiethCatalogueProofDagNodeBlock593_checker, twentiethCatalogueProofDagNodeBlock594_checker, twentiethCatalogueProofDagNodeBlock595_checker, twentiethCatalogueProofDagNodeBlock596_checker, twentiethCatalogueProofDagNodeBlock597_checker, twentiethCatalogueProofDagNodeBlock598_checker, twentiethCatalogueProofDagNodeBlock599_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
