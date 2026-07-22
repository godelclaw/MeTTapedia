import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock072_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 72 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock073_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 73 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock074_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 74 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock075_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 75 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock076_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 76 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock077_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 77 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock078_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 78 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock079_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 79 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 009. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk009_checker
    (block : Nat) (hlower : 72 ≤ block) (hupper : block < 80) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock072_checker,
      twentiethCatalogueOrbitProofDagNodeBlock073_checker,
      twentiethCatalogueOrbitProofDagNodeBlock074_checker,
      twentiethCatalogueOrbitProofDagNodeBlock075_checker,
      twentiethCatalogueOrbitProofDagNodeBlock076_checker,
      twentiethCatalogueOrbitProofDagNodeBlock077_checker,
      twentiethCatalogueOrbitProofDagNodeBlock078_checker,
      twentiethCatalogueOrbitProofDagNodeBlock079_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
