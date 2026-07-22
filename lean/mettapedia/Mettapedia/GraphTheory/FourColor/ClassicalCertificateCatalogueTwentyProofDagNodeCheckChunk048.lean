import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock384_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 384 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock385_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 385 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock386_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 386 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock387_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 387 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock388_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 388 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock389_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 389 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock390_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 390 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock391_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 391 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 048. -/
theorem twentiethCatalogueProofDagNodeChunk048_checker
    (block : Nat) (hlower : 384 ≤ block) (hupper : block < 392) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock384_checker, twentiethCatalogueProofDagNodeBlock385_checker, twentiethCatalogueProofDagNodeBlock386_checker, twentiethCatalogueProofDagNodeBlock387_checker, twentiethCatalogueProofDagNodeBlock388_checker, twentiethCatalogueProofDagNodeBlock389_checker, twentiethCatalogueProofDagNodeBlock390_checker, twentiethCatalogueProofDagNodeBlock391_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
