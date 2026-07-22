import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock272_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 272 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock273_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 273 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock274_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 274 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock275_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 275 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock276_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 276 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock277_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 277 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock278_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 278 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock279_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 279 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 034. -/
theorem twentiethCatalogueProofDagNodeChunk034_checker
    (block : Nat) (hlower : 272 ≤ block) (hupper : block < 280) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock272_checker, twentiethCatalogueProofDagNodeBlock273_checker, twentiethCatalogueProofDagNodeBlock274_checker, twentiethCatalogueProofDagNodeBlock275_checker, twentiethCatalogueProofDagNodeBlock276_checker, twentiethCatalogueProofDagNodeBlock277_checker, twentiethCatalogueProofDagNodeBlock278_checker, twentiethCatalogueProofDagNodeBlock279_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
