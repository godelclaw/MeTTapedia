import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock328_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 328 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock329_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 329 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock330_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 330 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock331_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 331 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock332_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 332 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock333_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 333 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock334_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 334 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock335_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 335 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 041. -/
theorem twentiethCatalogueProofDagNodeChunk041_checker
    (block : Nat) (hlower : 328 ≤ block) (hupper : block < 336) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock328_checker, twentiethCatalogueProofDagNodeBlock329_checker, twentiethCatalogueProofDagNodeBlock330_checker, twentiethCatalogueProofDagNodeBlock331_checker, twentiethCatalogueProofDagNodeBlock332_checker, twentiethCatalogueProofDagNodeBlock333_checker, twentiethCatalogueProofDagNodeBlock334_checker, twentiethCatalogueProofDagNodeBlock335_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
