import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock096_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 96 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock097_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 97 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock098_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 98 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock099_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 99 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock100_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 100 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock101_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 101 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock102_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 102 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock103_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 103 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 012. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk012_checker
    (block : Nat) (hlower : 96 ≤ block) (hupper : block < 104) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock096_checker,
      twentiethCatalogueOrbitProofDagNodeBlock097_checker,
      twentiethCatalogueOrbitProofDagNodeBlock098_checker,
      twentiethCatalogueOrbitProofDagNodeBlock099_checker,
      twentiethCatalogueOrbitProofDagNodeBlock100_checker,
      twentiethCatalogueOrbitProofDagNodeBlock101_checker,
      twentiethCatalogueOrbitProofDagNodeBlock102_checker,
      twentiethCatalogueOrbitProofDagNodeBlock103_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
