import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock400_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 400 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock401_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 401 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock402_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 402 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock403_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 403 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock404_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 404 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock405_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 405 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock406_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 406 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock407_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 407 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 050. -/
theorem twentiethCatalogueProofDagNodeChunk050_checker
    (block : Nat) (hlower : 400 ≤ block) (hupper : block < 408) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock400_checker, twentiethCatalogueProofDagNodeBlock401_checker, twentiethCatalogueProofDagNodeBlock402_checker, twentiethCatalogueProofDagNodeBlock403_checker, twentiethCatalogueProofDagNodeBlock404_checker, twentiethCatalogueProofDagNodeBlock405_checker, twentiethCatalogueProofDagNodeBlock406_checker, twentiethCatalogueProofDagNodeBlock407_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
