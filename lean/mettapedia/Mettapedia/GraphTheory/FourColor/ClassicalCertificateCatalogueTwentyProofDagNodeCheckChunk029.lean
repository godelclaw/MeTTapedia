import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock232_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 232 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock233_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 233 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock234_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 234 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock235_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 235 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock236_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 236 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock237_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 237 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock238_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 238 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock239_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 239 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 029. -/
theorem twentiethCatalogueProofDagNodeChunk029_checker
    (block : Nat) (hlower : 232 ≤ block) (hupper : block < 240) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock232_checker, twentiethCatalogueProofDagNodeBlock233_checker, twentiethCatalogueProofDagNodeBlock234_checker, twentiethCatalogueProofDagNodeBlock235_checker, twentiethCatalogueProofDagNodeBlock236_checker, twentiethCatalogueProofDagNodeBlock237_checker, twentiethCatalogueProofDagNodeBlock238_checker, twentiethCatalogueProofDagNodeBlock239_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
