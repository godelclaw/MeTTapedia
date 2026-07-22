import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock296_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 296 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock297_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 297 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock298_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 298 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock299_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 299 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock300_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 300 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock301_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 301 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock302_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 302 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock303_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 303 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 037. -/
theorem twentiethCatalogueProofDagNodeChunk037_checker
    (block : Nat) (hlower : 296 ≤ block) (hupper : block < 304) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock296_checker, twentiethCatalogueProofDagNodeBlock297_checker, twentiethCatalogueProofDagNodeBlock298_checker, twentiethCatalogueProofDagNodeBlock299_checker, twentiethCatalogueProofDagNodeBlock300_checker, twentiethCatalogueProofDagNodeBlock301_checker, twentiethCatalogueProofDagNodeBlock302_checker, twentiethCatalogueProofDagNodeBlock303_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
