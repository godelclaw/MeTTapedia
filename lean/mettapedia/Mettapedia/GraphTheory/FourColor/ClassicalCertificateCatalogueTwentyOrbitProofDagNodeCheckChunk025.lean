import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock200_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 200 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock201_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 201 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock202_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 202 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock203_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 203 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock204_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 204 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock205_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 205 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock206_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 206 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock207_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 207 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 025. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk025_checker
    (block : Nat) (hlower : 200 ≤ block) (hupper : block < 208) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock200_checker,
      twentiethCatalogueOrbitProofDagNodeBlock201_checker,
      twentiethCatalogueOrbitProofDagNodeBlock202_checker,
      twentiethCatalogueOrbitProofDagNodeBlock203_checker,
      twentiethCatalogueOrbitProofDagNodeBlock204_checker,
      twentiethCatalogueOrbitProofDagNodeBlock205_checker,
      twentiethCatalogueOrbitProofDagNodeBlock206_checker,
      twentiethCatalogueOrbitProofDagNodeBlock207_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
