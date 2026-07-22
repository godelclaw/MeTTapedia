import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock000_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 0 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock001_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 1 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock002_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 2 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock003_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 3 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock004_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 4 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock005_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 5 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock006_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 6 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock007_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 7 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 000. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk000_checker
    (block : Nat) (hlower : 0 ≤ block) (hupper : block < 8) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock000_checker,
      twentiethCatalogueOrbitProofDagNodeBlock001_checker,
      twentiethCatalogueOrbitProofDagNodeBlock002_checker,
      twentiethCatalogueOrbitProofDagNodeBlock003_checker,
      twentiethCatalogueOrbitProofDagNodeBlock004_checker,
      twentiethCatalogueOrbitProofDagNodeBlock005_checker,
      twentiethCatalogueOrbitProofDagNodeBlock006_checker,
      twentiethCatalogueOrbitProofDagNodeBlock007_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
