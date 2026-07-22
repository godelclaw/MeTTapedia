import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock288_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 288 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock289_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 289 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock290_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 290 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock291_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 291 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock292_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 292 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock293_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 293 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock294_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 294 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock295_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 295 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 036. -/
theorem twentiethCatalogueProofDagNodeChunk036_checker
    (block : Nat) (hlower : 288 ≤ block) (hupper : block < 296) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock288_checker, twentiethCatalogueProofDagNodeBlock289_checker, twentiethCatalogueProofDagNodeBlock290_checker, twentiethCatalogueProofDagNodeBlock291_checker, twentiethCatalogueProofDagNodeBlock292_checker, twentiethCatalogueProofDagNodeBlock293_checker, twentiethCatalogueProofDagNodeBlock294_checker, twentiethCatalogueProofDagNodeBlock295_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
