import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock048_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 48 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock049_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 49 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock050_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 50 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock051_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 51 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock052_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 52 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock053_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 53 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock054_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 54 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock055_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 55 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 006. -/
theorem twentiethCatalogueProofDagNodeChunk006_checker
    (block : Nat) (hlower : 48 ≤ block) (hupper : block < 56) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock048_checker, twentiethCatalogueProofDagNodeBlock049_checker, twentiethCatalogueProofDagNodeBlock050_checker, twentiethCatalogueProofDagNodeBlock051_checker, twentiethCatalogueProofDagNodeBlock052_checker, twentiethCatalogueProofDagNodeBlock053_checker, twentiethCatalogueProofDagNodeBlock054_checker, twentiethCatalogueProofDagNodeBlock055_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
