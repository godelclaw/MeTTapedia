import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock600_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 600 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock601_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 601 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock602_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 602 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock603_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 603 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock604_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 604 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock605_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 605 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock606_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 606 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock607_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 607 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 075. -/
theorem twentiethCatalogueProofDagNodeChunk075_checker
    (block : Nat) (hlower : 600 ≤ block) (hupper : block < 608) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock600_checker, twentiethCatalogueProofDagNodeBlock601_checker, twentiethCatalogueProofDagNodeBlock602_checker, twentiethCatalogueProofDagNodeBlock603_checker, twentiethCatalogueProofDagNodeBlock604_checker, twentiethCatalogueProofDagNodeBlock605_checker, twentiethCatalogueProofDagNodeBlock606_checker, twentiethCatalogueProofDagNodeBlock607_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
