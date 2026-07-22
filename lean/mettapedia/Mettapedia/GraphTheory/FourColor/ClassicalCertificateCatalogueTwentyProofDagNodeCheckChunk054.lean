import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock432_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 432 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock433_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 433 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock434_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 434 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock435_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 435 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock436_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 436 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock437_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 437 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock438_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 438 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock439_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 439 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 054. -/
theorem twentiethCatalogueProofDagNodeChunk054_checker
    (block : Nat) (hlower : 432 ≤ block) (hupper : block < 440) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock432_checker, twentiethCatalogueProofDagNodeBlock433_checker, twentiethCatalogueProofDagNodeBlock434_checker, twentiethCatalogueProofDagNodeBlock435_checker, twentiethCatalogueProofDagNodeBlock436_checker, twentiethCatalogueProofDagNodeBlock437_checker, twentiethCatalogueProofDagNodeBlock438_checker, twentiethCatalogueProofDagNodeBlock439_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
