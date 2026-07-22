import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock448_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 448 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock449_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 449 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock450_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 450 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock451_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 451 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock452_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 452 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock453_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 453 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock454_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 454 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock455_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 455 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 056. -/
theorem twentiethCatalogueProofDagNodeChunk056_checker
    (block : Nat) (hlower : 448 ≤ block) (hupper : block < 456) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock448_checker, twentiethCatalogueProofDagNodeBlock449_checker, twentiethCatalogueProofDagNodeBlock450_checker, twentiethCatalogueProofDagNodeBlock451_checker, twentiethCatalogueProofDagNodeBlock452_checker, twentiethCatalogueProofDagNodeBlock453_checker, twentiethCatalogueProofDagNodeBlock454_checker, twentiethCatalogueProofDagNodeBlock455_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
