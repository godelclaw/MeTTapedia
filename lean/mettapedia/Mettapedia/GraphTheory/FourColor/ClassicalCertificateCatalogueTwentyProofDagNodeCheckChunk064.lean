import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock512_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 512 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock513_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 513 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock514_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 514 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock515_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 515 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock516_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 516 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock517_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 517 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock518_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 518 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock519_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 519 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 064. -/
theorem twentiethCatalogueProofDagNodeChunk064_checker
    (block : Nat) (hlower : 512 ≤ block) (hupper : block < 520) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock512_checker, twentiethCatalogueProofDagNodeBlock513_checker, twentiethCatalogueProofDagNodeBlock514_checker, twentiethCatalogueProofDagNodeBlock515_checker, twentiethCatalogueProofDagNodeBlock516_checker, twentiethCatalogueProofDagNodeBlock517_checker, twentiethCatalogueProofDagNodeBlock518_checker, twentiethCatalogueProofDagNodeBlock519_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
