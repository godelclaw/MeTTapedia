import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock048_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 48 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock049_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 49 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock050_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 50 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock051_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 51 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock052_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 52 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock053_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 53 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock054_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 54 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock055_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 55 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 006. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk006_checker
    (block : Nat) (hlower : 48 ≤ block) (hupper : block < 56) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock048_checker,
      twentiethCatalogueOrbitProofDagNodeBlock049_checker,
      twentiethCatalogueOrbitProofDagNodeBlock050_checker,
      twentiethCatalogueOrbitProofDagNodeBlock051_checker,
      twentiethCatalogueOrbitProofDagNodeBlock052_checker,
      twentiethCatalogueOrbitProofDagNodeBlock053_checker,
      twentiethCatalogueOrbitProofDagNodeBlock054_checker,
      twentiethCatalogueOrbitProofDagNodeBlock055_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
