import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock032_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 32 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock033_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 33 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock034_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 34 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock035_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 35 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock036_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 36 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock037_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 37 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock038_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 38 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock039_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 39 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 004. -/
theorem twentiethCatalogueProofDagNodeChunk004_checker
    (block : Nat) (hlower : 32 ≤ block) (hupper : block < 40) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock032_checker, twentiethCatalogueProofDagNodeBlock033_checker, twentiethCatalogueProofDagNodeBlock034_checker, twentiethCatalogueProofDagNodeBlock035_checker, twentiethCatalogueProofDagNodeBlock036_checker, twentiethCatalogueProofDagNodeBlock037_checker, twentiethCatalogueProofDagNodeBlock038_checker, twentiethCatalogueProofDagNodeBlock039_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
