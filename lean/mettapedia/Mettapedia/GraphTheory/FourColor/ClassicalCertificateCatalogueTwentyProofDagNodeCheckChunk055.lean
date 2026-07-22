import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock440_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 440 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock441_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 441 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock442_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 442 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock443_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 443 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock444_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 444 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock445_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 445 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock446_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 446 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock447_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 447 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 055. -/
theorem twentiethCatalogueProofDagNodeChunk055_checker
    (block : Nat) (hlower : 440 ≤ block) (hupper : block < 448) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock440_checker, twentiethCatalogueProofDagNodeBlock441_checker, twentiethCatalogueProofDagNodeBlock442_checker, twentiethCatalogueProofDagNodeBlock443_checker, twentiethCatalogueProofDagNodeBlock444_checker, twentiethCatalogueProofDagNodeBlock445_checker, twentiethCatalogueProofDagNodeBlock446_checker, twentiethCatalogueProofDagNodeBlock447_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
