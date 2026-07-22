import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock632_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 632 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock633_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 633 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock634_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 634 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock635_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 635 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock636_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 636 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock637_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 637 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock638_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 638 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock639_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 639 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 079. -/
theorem twentiethCatalogueProofDagNodeChunk079_checker
    (block : Nat) (hlower : 632 ≤ block) (hupper : block < 640) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock632_checker, twentiethCatalogueProofDagNodeBlock633_checker, twentiethCatalogueProofDagNodeBlock634_checker, twentiethCatalogueProofDagNodeBlock635_checker, twentiethCatalogueProofDagNodeBlock636_checker, twentiethCatalogueProofDagNodeBlock637_checker, twentiethCatalogueProofDagNodeBlock638_checker, twentiethCatalogueProofDagNodeBlock639_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
