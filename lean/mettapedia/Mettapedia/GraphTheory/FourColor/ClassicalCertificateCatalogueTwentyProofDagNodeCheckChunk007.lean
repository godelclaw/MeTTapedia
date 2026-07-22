import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock056_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 56 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock057_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 57 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock058_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 58 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock059_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 59 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock060_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 60 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock061_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 61 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock062_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 62 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock063_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 63 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 007. -/
theorem twentiethCatalogueProofDagNodeChunk007_checker
    (block : Nat) (hlower : 56 ≤ block) (hupper : block < 64) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock056_checker, twentiethCatalogueProofDagNodeBlock057_checker, twentiethCatalogueProofDagNodeBlock058_checker, twentiethCatalogueProofDagNodeBlock059_checker, twentiethCatalogueProofDagNodeBlock060_checker, twentiethCatalogueProofDagNodeBlock061_checker, twentiethCatalogueProofDagNodeBlock062_checker, twentiethCatalogueProofDagNodeBlock063_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
