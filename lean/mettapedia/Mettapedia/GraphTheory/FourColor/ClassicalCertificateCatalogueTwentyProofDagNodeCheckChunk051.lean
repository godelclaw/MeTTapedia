import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock408_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 408 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock409_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 409 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock410_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 410 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock411_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 411 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock412_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 412 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock413_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 413 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock414_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 414 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock415_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 415 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 051. -/
theorem twentiethCatalogueProofDagNodeChunk051_checker
    (block : Nat) (hlower : 408 ≤ block) (hupper : block < 416) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock408_checker, twentiethCatalogueProofDagNodeBlock409_checker, twentiethCatalogueProofDagNodeBlock410_checker, twentiethCatalogueProofDagNodeBlock411_checker, twentiethCatalogueProofDagNodeBlock412_checker, twentiethCatalogueProofDagNodeBlock413_checker, twentiethCatalogueProofDagNodeBlock414_checker, twentiethCatalogueProofDagNodeBlock415_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
