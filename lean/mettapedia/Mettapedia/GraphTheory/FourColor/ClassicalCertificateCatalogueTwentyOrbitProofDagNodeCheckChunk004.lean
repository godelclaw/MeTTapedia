import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock032_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 32 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock033_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 33 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock034_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 34 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock035_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 35 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock036_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 36 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock037_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 37 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock038_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 38 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock039_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 39 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 004. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk004_checker
    (block : Nat) (hlower : 32 ≤ block) (hupper : block < 40) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock032_checker,
      twentiethCatalogueOrbitProofDagNodeBlock033_checker,
      twentiethCatalogueOrbitProofDagNodeBlock034_checker,
      twentiethCatalogueOrbitProofDagNodeBlock035_checker,
      twentiethCatalogueOrbitProofDagNodeBlock036_checker,
      twentiethCatalogueOrbitProofDagNodeBlock037_checker,
      twentiethCatalogueOrbitProofDagNodeBlock038_checker,
      twentiethCatalogueOrbitProofDagNodeBlock039_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
