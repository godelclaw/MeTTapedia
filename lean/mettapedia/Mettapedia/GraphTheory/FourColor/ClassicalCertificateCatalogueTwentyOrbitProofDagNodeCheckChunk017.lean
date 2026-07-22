import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock136_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 136 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock137_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 137 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock138_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 138 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock139_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 139 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock140_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 140 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock141_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 141 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock142_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 142 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock143_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 143 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 017. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk017_checker
    (block : Nat) (hlower : 136 ≤ block) (hupper : block < 144) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock136_checker,
      twentiethCatalogueOrbitProofDagNodeBlock137_checker,
      twentiethCatalogueOrbitProofDagNodeBlock138_checker,
      twentiethCatalogueOrbitProofDagNodeBlock139_checker,
      twentiethCatalogueOrbitProofDagNodeBlock140_checker,
      twentiethCatalogueOrbitProofDagNodeBlock141_checker,
      twentiethCatalogueOrbitProofDagNodeBlock142_checker,
      twentiethCatalogueOrbitProofDagNodeBlock143_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
