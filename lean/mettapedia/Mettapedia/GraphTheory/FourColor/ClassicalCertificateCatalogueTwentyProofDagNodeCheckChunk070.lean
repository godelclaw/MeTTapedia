import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock560_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 560 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock561_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 561 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock562_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 562 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock563_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 563 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock564_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 564 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock565_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 565 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock566_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 566 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock567_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 567 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 070. -/
theorem twentiethCatalogueProofDagNodeChunk070_checker
    (block : Nat) (hlower : 560 ≤ block) (hupper : block < 568) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock560_checker, twentiethCatalogueProofDagNodeBlock561_checker, twentiethCatalogueProofDagNodeBlock562_checker, twentiethCatalogueProofDagNodeBlock563_checker, twentiethCatalogueProofDagNodeBlock564_checker, twentiethCatalogueProofDagNodeBlock565_checker, twentiethCatalogueProofDagNodeBlock566_checker, twentiethCatalogueProofDagNodeBlock567_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
