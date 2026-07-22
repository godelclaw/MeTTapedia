import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock064_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 64 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock065_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 65 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock066_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 66 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock067_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 67 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock068_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 68 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock069_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 69 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock070_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 70 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock071_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 71 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 008. -/
theorem twentiethCatalogueProofDagNodeChunk008_checker
    (block : Nat) (hlower : 64 ≤ block) (hupper : block < 72) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock064_checker, twentiethCatalogueProofDagNodeBlock065_checker, twentiethCatalogueProofDagNodeBlock066_checker, twentiethCatalogueProofDagNodeBlock067_checker, twentiethCatalogueProofDagNodeBlock068_checker, twentiethCatalogueProofDagNodeBlock069_checker, twentiethCatalogueProofDagNodeBlock070_checker, twentiethCatalogueProofDagNodeBlock071_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
