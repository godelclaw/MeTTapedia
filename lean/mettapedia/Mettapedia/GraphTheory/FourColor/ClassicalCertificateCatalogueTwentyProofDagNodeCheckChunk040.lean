import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock320_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 320 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock321_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 321 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock322_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 322 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock323_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 323 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock324_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 324 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock325_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 325 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock326_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 326 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock327_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 327 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 040. -/
theorem twentiethCatalogueProofDagNodeChunk040_checker
    (block : Nat) (hlower : 320 ≤ block) (hupper : block < 328) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock320_checker, twentiethCatalogueProofDagNodeBlock321_checker, twentiethCatalogueProofDagNodeBlock322_checker, twentiethCatalogueProofDagNodeBlock323_checker, twentiethCatalogueProofDagNodeBlock324_checker, twentiethCatalogueProofDagNodeBlock325_checker, twentiethCatalogueProofDagNodeBlock326_checker, twentiethCatalogueProofDagNodeBlock327_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
