import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock096_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 96 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock097_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 97 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock098_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 98 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock099_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 99 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock100_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 100 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock101_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 101 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock102_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 102 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock103_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 103 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 012. -/
theorem twentiethCatalogueProofDagNodeChunk012_checker
    (block : Nat) (hlower : 96 ≤ block) (hupper : block < 104) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock096_checker, twentiethCatalogueProofDagNodeBlock097_checker, twentiethCatalogueProofDagNodeBlock098_checker, twentiethCatalogueProofDagNodeBlock099_checker, twentiethCatalogueProofDagNodeBlock100_checker, twentiethCatalogueProofDagNodeBlock101_checker, twentiethCatalogueProofDagNodeBlock102_checker, twentiethCatalogueProofDagNodeBlock103_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
