import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock152_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 152 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock153_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 153 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock154_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 154 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock155_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 155 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock156_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 156 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock157_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 157 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock158_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 158 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock159_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 159 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 019. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk019_checker
    (block : Nat) (hlower : 152 ≤ block) (hupper : block < 160) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock152_checker,
      twentiethCatalogueOrbitProofDagNodeBlock153_checker,
      twentiethCatalogueOrbitProofDagNodeBlock154_checker,
      twentiethCatalogueOrbitProofDagNodeBlock155_checker,
      twentiethCatalogueOrbitProofDagNodeBlock156_checker,
      twentiethCatalogueOrbitProofDagNodeBlock157_checker,
      twentiethCatalogueOrbitProofDagNodeBlock158_checker,
      twentiethCatalogueOrbitProofDagNodeBlock159_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
