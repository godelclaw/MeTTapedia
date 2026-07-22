import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock040_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 40 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock041_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 41 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock042_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 42 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock043_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 43 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock044_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 44 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock045_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 45 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock046_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 46 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock047_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 47 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 005. -/
theorem twentiethCatalogueProofDagNodeChunk005_checker
    (block : Nat) (hlower : 40 ≤ block) (hupper : block < 48) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock040_checker, twentiethCatalogueProofDagNodeBlock041_checker, twentiethCatalogueProofDagNodeBlock042_checker, twentiethCatalogueProofDagNodeBlock043_checker, twentiethCatalogueProofDagNodeBlock044_checker, twentiethCatalogueProofDagNodeBlock045_checker, twentiethCatalogueProofDagNodeBlock046_checker, twentiethCatalogueProofDagNodeBlock047_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
