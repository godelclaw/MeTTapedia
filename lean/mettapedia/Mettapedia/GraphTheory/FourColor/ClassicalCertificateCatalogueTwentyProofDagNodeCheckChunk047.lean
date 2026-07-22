import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock376_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 376 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock377_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 377 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock378_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 378 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock379_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 379 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock380_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 380 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock381_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 381 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock382_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 382 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock383_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 383 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 047. -/
theorem twentiethCatalogueProofDagNodeChunk047_checker
    (block : Nat) (hlower : 376 ≤ block) (hupper : block < 384) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock376_checker, twentiethCatalogueProofDagNodeBlock377_checker, twentiethCatalogueProofDagNodeBlock378_checker, twentiethCatalogueProofDagNodeBlock379_checker, twentiethCatalogueProofDagNodeBlock380_checker, twentiethCatalogueProofDagNodeBlock381_checker, twentiethCatalogueProofDagNodeBlock382_checker, twentiethCatalogueProofDagNodeBlock383_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
