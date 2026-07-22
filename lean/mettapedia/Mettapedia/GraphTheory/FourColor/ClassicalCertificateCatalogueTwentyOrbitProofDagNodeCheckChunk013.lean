import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock104_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 104 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock105_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 105 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock106_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 106 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock107_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 107 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock108_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 108 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock109_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 109 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock110_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 110 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock111_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 111 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 013. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk013_checker
    (block : Nat) (hlower : 104 ≤ block) (hupper : block < 112) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock104_checker,
      twentiethCatalogueOrbitProofDagNodeBlock105_checker,
      twentiethCatalogueOrbitProofDagNodeBlock106_checker,
      twentiethCatalogueOrbitProofDagNodeBlock107_checker,
      twentiethCatalogueOrbitProofDagNodeBlock108_checker,
      twentiethCatalogueOrbitProofDagNodeBlock109_checker,
      twentiethCatalogueOrbitProofDagNodeBlock110_checker,
      twentiethCatalogueOrbitProofDagNodeBlock111_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
