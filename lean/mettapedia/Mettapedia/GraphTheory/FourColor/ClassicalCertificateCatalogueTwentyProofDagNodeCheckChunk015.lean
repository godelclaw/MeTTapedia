import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock120_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 120 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock121_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 121 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock122_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 122 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock123_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 123 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock124_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 124 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock125_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 125 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock126_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 126 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock127_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 127 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 015. -/
theorem twentiethCatalogueProofDagNodeChunk015_checker
    (block : Nat) (hlower : 120 ≤ block) (hupper : block < 128) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock120_checker, twentiethCatalogueProofDagNodeBlock121_checker, twentiethCatalogueProofDagNodeBlock122_checker, twentiethCatalogueProofDagNodeBlock123_checker, twentiethCatalogueProofDagNodeBlock124_checker, twentiethCatalogueProofDagNodeBlock125_checker, twentiethCatalogueProofDagNodeBlock126_checker, twentiethCatalogueProofDagNodeBlock127_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
