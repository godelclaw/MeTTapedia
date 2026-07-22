import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock360_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 360 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock361_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 361 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock362_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 362 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock363_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 363 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock364_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 364 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock365_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 365 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock366_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 366 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock367_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 367 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 045. -/
theorem twentiethCatalogueProofDagNodeChunk045_checker
    (block : Nat) (hlower : 360 ≤ block) (hupper : block < 368) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock360_checker, twentiethCatalogueProofDagNodeBlock361_checker, twentiethCatalogueProofDagNodeBlock362_checker, twentiethCatalogueProofDagNodeBlock363_checker, twentiethCatalogueProofDagNodeBlock364_checker, twentiethCatalogueProofDagNodeBlock365_checker, twentiethCatalogueProofDagNodeBlock366_checker, twentiethCatalogueProofDagNodeBlock367_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
