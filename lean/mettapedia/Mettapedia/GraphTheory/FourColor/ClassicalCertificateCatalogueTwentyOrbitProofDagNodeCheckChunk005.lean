import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock040_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 40 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock041_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 41 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock042_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 42 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock043_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 43 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock044_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 44 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock045_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 45 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock046_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 46 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock047_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 47 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 005. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk005_checker
    (block : Nat) (hlower : 40 ≤ block) (hupper : block < 48) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock040_checker,
      twentiethCatalogueOrbitProofDagNodeBlock041_checker,
      twentiethCatalogueOrbitProofDagNodeBlock042_checker,
      twentiethCatalogueOrbitProofDagNodeBlock043_checker,
      twentiethCatalogueOrbitProofDagNodeBlock044_checker,
      twentiethCatalogueOrbitProofDagNodeBlock045_checker,
      twentiethCatalogueOrbitProofDagNodeBlock046_checker,
      twentiethCatalogueOrbitProofDagNodeBlock047_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
