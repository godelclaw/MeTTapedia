import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock480_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 480 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock481_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 481 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock482_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 482 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock483_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 483 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock484_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 484 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock485_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 485 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock486_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 486 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock487_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 487 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 060. -/
theorem twentiethCatalogueProofDagNodeChunk060_checker
    (block : Nat) (hlower : 480 ≤ block) (hupper : block < 488) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock480_checker, twentiethCatalogueProofDagNodeBlock481_checker, twentiethCatalogueProofDagNodeBlock482_checker, twentiethCatalogueProofDagNodeBlock483_checker, twentiethCatalogueProofDagNodeBlock484_checker, twentiethCatalogueProofDagNodeBlock485_checker, twentiethCatalogueProofDagNodeBlock486_checker, twentiethCatalogueProofDagNodeBlock487_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
