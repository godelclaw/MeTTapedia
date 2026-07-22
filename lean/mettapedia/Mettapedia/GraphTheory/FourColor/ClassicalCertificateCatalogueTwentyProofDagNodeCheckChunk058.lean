import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock464_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 464 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock465_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 465 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock466_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 466 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock467_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 467 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock468_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 468 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock469_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 469 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock470_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 470 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock471_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 471 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 058. -/
theorem twentiethCatalogueProofDagNodeChunk058_checker
    (block : Nat) (hlower : 464 ≤ block) (hupper : block < 472) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock464_checker, twentiethCatalogueProofDagNodeBlock465_checker, twentiethCatalogueProofDagNodeBlock466_checker, twentiethCatalogueProofDagNodeBlock467_checker, twentiethCatalogueProofDagNodeBlock468_checker, twentiethCatalogueProofDagNodeBlock469_checker, twentiethCatalogueProofDagNodeBlock470_checker, twentiethCatalogueProofDagNodeBlock471_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
