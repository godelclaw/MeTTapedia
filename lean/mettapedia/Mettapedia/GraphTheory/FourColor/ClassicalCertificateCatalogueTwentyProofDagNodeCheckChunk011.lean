import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock088_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 88 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock089_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 89 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock090_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 90 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock091_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 91 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock092_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 92 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock093_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 93 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock094_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 94 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock095_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 95 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 011. -/
theorem twentiethCatalogueProofDagNodeChunk011_checker
    (block : Nat) (hlower : 88 ≤ block) (hupper : block < 96) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock088_checker, twentiethCatalogueProofDagNodeBlock089_checker, twentiethCatalogueProofDagNodeBlock090_checker, twentiethCatalogueProofDagNodeBlock091_checker, twentiethCatalogueProofDagNodeBlock092_checker, twentiethCatalogueProofDagNodeBlock093_checker, twentiethCatalogueProofDagNodeBlock094_checker, twentiethCatalogueProofDagNodeBlock095_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
