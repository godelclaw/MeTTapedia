import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock080_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 80 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock081_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 81 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock082_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 82 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock083_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 83 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock084_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 84 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock085_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 85 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock086_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 86 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock087_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 87 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 010. -/
theorem twentiethCatalogueProofDagNodeChunk010_checker
    (block : Nat) (hlower : 80 ≤ block) (hupper : block < 88) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock080_checker, twentiethCatalogueProofDagNodeBlock081_checker, twentiethCatalogueProofDagNodeBlock082_checker, twentiethCatalogueProofDagNodeBlock083_checker, twentiethCatalogueProofDagNodeBlock084_checker, twentiethCatalogueProofDagNodeBlock085_checker, twentiethCatalogueProofDagNodeBlock086_checker, twentiethCatalogueProofDagNodeBlock087_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
