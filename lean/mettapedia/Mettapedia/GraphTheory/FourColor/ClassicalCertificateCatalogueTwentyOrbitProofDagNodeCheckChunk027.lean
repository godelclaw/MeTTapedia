import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock216_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 216 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock217_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 217 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock218_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 218 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock219_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 219 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock220_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 220 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock221_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 221 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock222_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 222 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock223_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 223 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 027. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk027_checker
    (block : Nat) (hlower : 216 ≤ block) (hupper : block < 224) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock216_checker,
      twentiethCatalogueOrbitProofDagNodeBlock217_checker,
      twentiethCatalogueOrbitProofDagNodeBlock218_checker,
      twentiethCatalogueOrbitProofDagNodeBlock219_checker,
      twentiethCatalogueOrbitProofDagNodeBlock220_checker,
      twentiethCatalogueOrbitProofDagNodeBlock221_checker,
      twentiethCatalogueOrbitProofDagNodeBlock222_checker,
      twentiethCatalogueOrbitProofDagNodeBlock223_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
