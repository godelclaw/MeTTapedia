import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock240_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 240 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock241_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 241 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock242_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 242 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock243_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 243 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock244_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 244 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock245_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 245 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock246_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 246 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock247_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 247 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 030. -/
theorem twentiethCatalogueProofDagNodeChunk030_checker
    (block : Nat) (hlower : 240 ≤ block) (hupper : block < 248) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock240_checker, twentiethCatalogueProofDagNodeBlock241_checker, twentiethCatalogueProofDagNodeBlock242_checker, twentiethCatalogueProofDagNodeBlock243_checker, twentiethCatalogueProofDagNodeBlock244_checker, twentiethCatalogueProofDagNodeBlock245_checker, twentiethCatalogueProofDagNodeBlock246_checker, twentiethCatalogueProofDagNodeBlock247_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
