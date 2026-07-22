import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock352_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 352 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock353_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 353 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock354_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 354 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock355_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 355 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock356_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 356 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock357_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 357 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock358_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 358 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock359_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 359 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 044. -/
theorem twentiethCatalogueProofDagNodeChunk044_checker
    (block : Nat) (hlower : 352 ≤ block) (hupper : block < 360) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock352_checker, twentiethCatalogueProofDagNodeBlock353_checker, twentiethCatalogueProofDagNodeBlock354_checker, twentiethCatalogueProofDagNodeBlock355_checker, twentiethCatalogueProofDagNodeBlock356_checker, twentiethCatalogueProofDagNodeBlock357_checker, twentiethCatalogueProofDagNodeBlock358_checker, twentiethCatalogueProofDagNodeBlock359_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
