import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock080_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 80 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock081_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 81 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock082_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 82 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock083_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 83 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock084_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 84 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock085_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 85 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock086_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 86 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock087_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 87 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 010. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk010_checker
    (block : Nat) (hlower : 80 ≤ block) (hupper : block < 88) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock080_checker,
      twentiethCatalogueOrbitProofDagNodeBlock081_checker,
      twentiethCatalogueOrbitProofDagNodeBlock082_checker,
      twentiethCatalogueOrbitProofDagNodeBlock083_checker,
      twentiethCatalogueOrbitProofDagNodeBlock084_checker,
      twentiethCatalogueOrbitProofDagNodeBlock085_checker,
      twentiethCatalogueOrbitProofDagNodeBlock086_checker,
      twentiethCatalogueOrbitProofDagNodeBlock087_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
