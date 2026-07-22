import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock472_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 472 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock473_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 473 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock474_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 474 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock475_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 475 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock476_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 476 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock477_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 477 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock478_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 478 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock479_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 479 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 059. -/
theorem twentiethCatalogueProofDagNodeChunk059_checker
    (block : Nat) (hlower : 472 ≤ block) (hupper : block < 480) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock472_checker, twentiethCatalogueProofDagNodeBlock473_checker, twentiethCatalogueProofDagNodeBlock474_checker, twentiethCatalogueProofDagNodeBlock475_checker, twentiethCatalogueProofDagNodeBlock476_checker, twentiethCatalogueProofDagNodeBlock477_checker, twentiethCatalogueProofDagNodeBlock478_checker, twentiethCatalogueProofDagNodeBlock479_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
