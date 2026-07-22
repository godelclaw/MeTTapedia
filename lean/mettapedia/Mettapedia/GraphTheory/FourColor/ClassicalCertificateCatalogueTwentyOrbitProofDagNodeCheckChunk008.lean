import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock064_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 64 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock065_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 65 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock066_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 66 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock067_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 67 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock068_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 68 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock069_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 69 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock070_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 70 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock071_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 71 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 008. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk008_checker
    (block : Nat) (hlower : 64 ≤ block) (hupper : block < 72) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock064_checker,
      twentiethCatalogueOrbitProofDagNodeBlock065_checker,
      twentiethCatalogueOrbitProofDagNodeBlock066_checker,
      twentiethCatalogueOrbitProofDagNodeBlock067_checker,
      twentiethCatalogueOrbitProofDagNodeBlock068_checker,
      twentiethCatalogueOrbitProofDagNodeBlock069_checker,
      twentiethCatalogueOrbitProofDagNodeBlock070_checker,
      twentiethCatalogueOrbitProofDagNodeBlock071_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
