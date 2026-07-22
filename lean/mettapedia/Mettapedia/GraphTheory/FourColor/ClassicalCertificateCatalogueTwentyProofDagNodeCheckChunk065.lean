import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock520_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 520 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock521_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 521 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock522_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 522 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock523_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 523 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock524_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 524 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock525_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 525 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock526_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 526 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock527_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 527 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 065. -/
theorem twentiethCatalogueProofDagNodeChunk065_checker
    (block : Nat) (hlower : 520 ≤ block) (hupper : block < 528) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock520_checker, twentiethCatalogueProofDagNodeBlock521_checker, twentiethCatalogueProofDagNodeBlock522_checker, twentiethCatalogueProofDagNodeBlock523_checker, twentiethCatalogueProofDagNodeBlock524_checker, twentiethCatalogueProofDagNodeBlock525_checker, twentiethCatalogueProofDagNodeBlock526_checker, twentiethCatalogueProofDagNodeBlock527_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
