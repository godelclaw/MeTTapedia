import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock128_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 128 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock129_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 129 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock130_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 130 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock131_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 131 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock132_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 132 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock133_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 133 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock134_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 134 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock135_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 135 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 016. -/
theorem twentiethCatalogueProofDagNodeChunk016_checker
    (block : Nat) (hlower : 128 ≤ block) (hupper : block < 136) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock128_checker, twentiethCatalogueProofDagNodeBlock129_checker, twentiethCatalogueProofDagNodeBlock130_checker, twentiethCatalogueProofDagNodeBlock131_checker, twentiethCatalogueProofDagNodeBlock132_checker, twentiethCatalogueProofDagNodeBlock133_checker, twentiethCatalogueProofDagNodeBlock134_checker, twentiethCatalogueProofDagNodeBlock135_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
