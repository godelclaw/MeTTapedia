import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock584_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 584 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock585_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 585 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock586_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 586 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock587_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 587 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock588_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 588 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock589_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 589 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock590_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 590 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock591_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 591 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 073. -/
theorem twentiethCatalogueProofDagNodeChunk073_checker
    (block : Nat) (hlower : 584 ≤ block) (hupper : block < 592) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock584_checker, twentiethCatalogueProofDagNodeBlock585_checker, twentiethCatalogueProofDagNodeBlock586_checker, twentiethCatalogueProofDagNodeBlock587_checker, twentiethCatalogueProofDagNodeBlock588_checker, twentiethCatalogueProofDagNodeBlock589_checker, twentiethCatalogueProofDagNodeBlock590_checker, twentiethCatalogueProofDagNodeBlock591_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
