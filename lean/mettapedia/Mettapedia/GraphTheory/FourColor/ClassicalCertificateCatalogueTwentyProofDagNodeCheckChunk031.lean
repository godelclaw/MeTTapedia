import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock248_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 248 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock249_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 249 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock250_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 250 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock251_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 251 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock252_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 252 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock253_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 253 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock254_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 254 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock255_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 255 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 031. -/
theorem twentiethCatalogueProofDagNodeChunk031_checker
    (block : Nat) (hlower : 248 ≤ block) (hupper : block < 256) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock248_checker, twentiethCatalogueProofDagNodeBlock249_checker, twentiethCatalogueProofDagNodeBlock250_checker, twentiethCatalogueProofDagNodeBlock251_checker, twentiethCatalogueProofDagNodeBlock252_checker, twentiethCatalogueProofDagNodeBlock253_checker, twentiethCatalogueProofDagNodeBlock254_checker, twentiethCatalogueProofDagNodeBlock255_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
