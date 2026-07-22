import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock112_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 112 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock113_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 113 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock114_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 114 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock115_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 115 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock116_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 116 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock117_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 117 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock118_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 118 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock119_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 119 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 014. -/
theorem twentiethCatalogueProofDagNodeChunk014_checker
    (block : Nat) (hlower : 112 ≤ block) (hupper : block < 120) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock112_checker, twentiethCatalogueProofDagNodeBlock113_checker, twentiethCatalogueProofDagNodeBlock114_checker, twentiethCatalogueProofDagNodeBlock115_checker, twentiethCatalogueProofDagNodeBlock116_checker, twentiethCatalogueProofDagNodeBlock117_checker, twentiethCatalogueProofDagNodeBlock118_checker, twentiethCatalogueProofDagNodeBlock119_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
