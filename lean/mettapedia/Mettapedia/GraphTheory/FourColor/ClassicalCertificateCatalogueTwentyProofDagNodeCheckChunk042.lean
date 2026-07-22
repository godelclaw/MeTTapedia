import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock336_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 336 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock337_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 337 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock338_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 338 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock339_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 339 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock340_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 340 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock341_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 341 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock342_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 342 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock343_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 343 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 042. -/
theorem twentiethCatalogueProofDagNodeChunk042_checker
    (block : Nat) (hlower : 336 ≤ block) (hupper : block < 344) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock336_checker, twentiethCatalogueProofDagNodeBlock337_checker, twentiethCatalogueProofDagNodeBlock338_checker, twentiethCatalogueProofDagNodeBlock339_checker, twentiethCatalogueProofDagNodeBlock340_checker, twentiethCatalogueProofDagNodeBlock341_checker, twentiethCatalogueProofDagNodeBlock342_checker, twentiethCatalogueProofDagNodeBlock343_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
