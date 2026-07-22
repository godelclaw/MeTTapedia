import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock072_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 72 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock073_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 73 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock074_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 74 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock075_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 75 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock076_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 76 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock077_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 77 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock078_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 78 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock079_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 79 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 009. -/
theorem twentiethCatalogueProofDagNodeChunk009_checker
    (block : Nat) (hlower : 72 ≤ block) (hupper : block < 80) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock072_checker, twentiethCatalogueProofDagNodeBlock073_checker, twentiethCatalogueProofDagNodeBlock074_checker, twentiethCatalogueProofDagNodeBlock075_checker, twentiethCatalogueProofDagNodeBlock076_checker, twentiethCatalogueProofDagNodeBlock077_checker, twentiethCatalogueProofDagNodeBlock078_checker, twentiethCatalogueProofDagNodeBlock079_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
