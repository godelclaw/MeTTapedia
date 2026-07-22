import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock536_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 536 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock537_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 537 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock538_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 538 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock539_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 539 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock540_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 540 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock541_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 541 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock542_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 542 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock543_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 543 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 067. -/
theorem twentiethCatalogueProofDagNodeChunk067_checker
    (block : Nat) (hlower : 536 ≤ block) (hupper : block < 544) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock536_checker, twentiethCatalogueProofDagNodeBlock537_checker, twentiethCatalogueProofDagNodeBlock538_checker, twentiethCatalogueProofDagNodeBlock539_checker, twentiethCatalogueProofDagNodeBlock540_checker, twentiethCatalogueProofDagNodeBlock541_checker, twentiethCatalogueProofDagNodeBlock542_checker, twentiethCatalogueProofDagNodeBlock543_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
