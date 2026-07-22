import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock216_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 216 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock217_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 217 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock218_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 218 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock219_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 219 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock220_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 220 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock221_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 221 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock222_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 222 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock223_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 223 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 027. -/
theorem twentiethCatalogueProofDagNodeChunk027_checker
    (block : Nat) (hlower : 216 ≤ block) (hupper : block < 224) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock216_checker, twentiethCatalogueProofDagNodeBlock217_checker, twentiethCatalogueProofDagNodeBlock218_checker, twentiethCatalogueProofDagNodeBlock219_checker, twentiethCatalogueProofDagNodeBlock220_checker, twentiethCatalogueProofDagNodeBlock221_checker, twentiethCatalogueProofDagNodeBlock222_checker, twentiethCatalogueProofDagNodeBlock223_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
