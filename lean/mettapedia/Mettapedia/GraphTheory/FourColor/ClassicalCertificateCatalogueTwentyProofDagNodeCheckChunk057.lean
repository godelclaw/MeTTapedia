import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock456_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 456 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock457_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 457 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock458_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 458 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock459_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 459 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock460_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 460 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock461_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 461 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock462_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 462 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock463_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 463 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 057. -/
theorem twentiethCatalogueProofDagNodeChunk057_checker
    (block : Nat) (hlower : 456 ≤ block) (hupper : block < 464) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock456_checker, twentiethCatalogueProofDagNodeBlock457_checker, twentiethCatalogueProofDagNodeBlock458_checker, twentiethCatalogueProofDagNodeBlock459_checker, twentiethCatalogueProofDagNodeBlock460_checker, twentiethCatalogueProofDagNodeBlock461_checker, twentiethCatalogueProofDagNodeBlock462_checker, twentiethCatalogueProofDagNodeBlock463_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
