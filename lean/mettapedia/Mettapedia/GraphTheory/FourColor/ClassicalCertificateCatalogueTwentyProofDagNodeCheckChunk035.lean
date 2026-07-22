import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock280_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 280 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock281_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 281 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock282_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 282 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock283_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 283 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock284_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 284 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock285_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 285 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock286_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 286 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock287_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 287 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 035. -/
theorem twentiethCatalogueProofDagNodeChunk035_checker
    (block : Nat) (hlower : 280 ≤ block) (hupper : block < 288) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock280_checker, twentiethCatalogueProofDagNodeBlock281_checker, twentiethCatalogueProofDagNodeBlock282_checker, twentiethCatalogueProofDagNodeBlock283_checker, twentiethCatalogueProofDagNodeBlock284_checker, twentiethCatalogueProofDagNodeBlock285_checker, twentiethCatalogueProofDagNodeBlock286_checker, twentiethCatalogueProofDagNodeBlock287_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
