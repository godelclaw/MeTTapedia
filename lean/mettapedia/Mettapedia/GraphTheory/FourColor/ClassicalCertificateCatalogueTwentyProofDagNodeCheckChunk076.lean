import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock608_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 608 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock609_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 609 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock610_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 610 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock611_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 611 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock612_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 612 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock613_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 613 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock614_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 614 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock615_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 615 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 076. -/
theorem twentiethCatalogueProofDagNodeChunk076_checker
    (block : Nat) (hlower : 608 ≤ block) (hupper : block < 616) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock608_checker, twentiethCatalogueProofDagNodeBlock609_checker, twentiethCatalogueProofDagNodeBlock610_checker, twentiethCatalogueProofDagNodeBlock611_checker, twentiethCatalogueProofDagNodeBlock612_checker, twentiethCatalogueProofDagNodeBlock613_checker, twentiethCatalogueProofDagNodeBlock614_checker, twentiethCatalogueProofDagNodeBlock615_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
