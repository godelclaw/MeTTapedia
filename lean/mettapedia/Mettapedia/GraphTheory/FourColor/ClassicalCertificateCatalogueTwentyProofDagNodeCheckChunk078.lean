import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock624_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 624 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock625_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 625 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock626_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 626 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock627_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 627 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock628_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 628 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock629_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 629 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock630_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 630 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock631_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 631 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 078. -/
theorem twentiethCatalogueProofDagNodeChunk078_checker
    (block : Nat) (hlower : 624 ≤ block) (hupper : block < 632) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock624_checker, twentiethCatalogueProofDagNodeBlock625_checker, twentiethCatalogueProofDagNodeBlock626_checker, twentiethCatalogueProofDagNodeBlock627_checker, twentiethCatalogueProofDagNodeBlock628_checker, twentiethCatalogueProofDagNodeBlock629_checker, twentiethCatalogueProofDagNodeBlock630_checker, twentiethCatalogueProofDagNodeBlock631_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
