import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock088_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 88 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock089_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 89 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock090_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 90 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock091_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 91 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock092_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 92 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock093_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 93 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock094_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 94 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock095_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 95 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 011. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk011_checker
    (block : Nat) (hlower : 88 ≤ block) (hupper : block < 96) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock088_checker,
      twentiethCatalogueOrbitProofDagNodeBlock089_checker,
      twentiethCatalogueOrbitProofDagNodeBlock090_checker,
      twentiethCatalogueOrbitProofDagNodeBlock091_checker,
      twentiethCatalogueOrbitProofDagNodeBlock092_checker,
      twentiethCatalogueOrbitProofDagNodeBlock093_checker,
      twentiethCatalogueOrbitProofDagNodeBlock094_checker,
      twentiethCatalogueOrbitProofDagNodeBlock095_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
