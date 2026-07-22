import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock104_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 104 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock105_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 105 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock106_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 106 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock107_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 107 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock108_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 108 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock109_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 109 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock110_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 110 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock111_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 111 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 013. -/
theorem twentiethCatalogueProofDagNodeChunk013_checker
    (block : Nat) (hlower : 104 ≤ block) (hupper : block < 112) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock104_checker, twentiethCatalogueProofDagNodeBlock105_checker, twentiethCatalogueProofDagNodeBlock106_checker, twentiethCatalogueProofDagNodeBlock107_checker, twentiethCatalogueProofDagNodeBlock108_checker, twentiethCatalogueProofDagNodeBlock109_checker, twentiethCatalogueProofDagNodeBlock110_checker, twentiethCatalogueProofDagNodeBlock111_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
