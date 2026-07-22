import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock152_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 152 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock153_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 153 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock154_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 154 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock155_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 155 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock156_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 156 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock157_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 157 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock158_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 158 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock159_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 159 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 019. -/
theorem twentiethCatalogueProofDagNodeChunk019_checker
    (block : Nat) (hlower : 152 ≤ block) (hupper : block < 160) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock152_checker, twentiethCatalogueProofDagNodeBlock153_checker, twentiethCatalogueProofDagNodeBlock154_checker, twentiethCatalogueProofDagNodeBlock155_checker, twentiethCatalogueProofDagNodeBlock156_checker, twentiethCatalogueProofDagNodeBlock157_checker, twentiethCatalogueProofDagNodeBlock158_checker, twentiethCatalogueProofDagNodeBlock159_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
