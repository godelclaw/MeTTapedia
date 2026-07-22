import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock128_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 128 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock129_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 129 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock130_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 130 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock131_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 131 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock132_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 132 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock133_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 133 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock134_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 134 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock135_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 135 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 016. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk016_checker
    (block : Nat) (hlower : 128 ≤ block) (hupper : block < 136) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock128_checker,
      twentiethCatalogueOrbitProofDagNodeBlock129_checker,
      twentiethCatalogueOrbitProofDagNodeBlock130_checker,
      twentiethCatalogueOrbitProofDagNodeBlock131_checker,
      twentiethCatalogueOrbitProofDagNodeBlock132_checker,
      twentiethCatalogueOrbitProofDagNodeBlock133_checker,
      twentiethCatalogueOrbitProofDagNodeBlock134_checker,
      twentiethCatalogueOrbitProofDagNodeBlock135_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
