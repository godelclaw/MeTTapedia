import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock136_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 136 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock137_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 137 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock138_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 138 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock139_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 139 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock140_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 140 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock141_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 141 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock142_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 142 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock143_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 143 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 017. -/
theorem twentiethCatalogueProofDagNodeChunk017_checker
    (block : Nat) (hlower : 136 ≤ block) (hupper : block < 144) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock136_checker, twentiethCatalogueProofDagNodeBlock137_checker, twentiethCatalogueProofDagNodeBlock138_checker, twentiethCatalogueProofDagNodeBlock139_checker, twentiethCatalogueProofDagNodeBlock140_checker, twentiethCatalogueProofDagNodeBlock141_checker, twentiethCatalogueProofDagNodeBlock142_checker, twentiethCatalogueProofDagNodeBlock143_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
