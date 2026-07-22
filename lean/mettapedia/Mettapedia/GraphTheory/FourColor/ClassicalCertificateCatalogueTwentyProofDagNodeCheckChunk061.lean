import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock488_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 488 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock489_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 489 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock490_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 490 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock491_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 491 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock492_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 492 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock493_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 493 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock494_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 494 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock495_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 495 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 061. -/
theorem twentiethCatalogueProofDagNodeChunk061_checker
    (block : Nat) (hlower : 488 ≤ block) (hupper : block < 496) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock488_checker, twentiethCatalogueProofDagNodeBlock489_checker, twentiethCatalogueProofDagNodeBlock490_checker, twentiethCatalogueProofDagNodeBlock491_checker, twentiethCatalogueProofDagNodeBlock492_checker, twentiethCatalogueProofDagNodeBlock493_checker, twentiethCatalogueProofDagNodeBlock494_checker, twentiethCatalogueProofDagNodeBlock495_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
