import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock312_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 312 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock313_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 313 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock314_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 314 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock315_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 315 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock316_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 316 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock317_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 317 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock318_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 318 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock319_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 319 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 039. -/
theorem twentiethCatalogueProofDagNodeChunk039_checker
    (block : Nat) (hlower : 312 ≤ block) (hupper : block < 320) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock312_checker, twentiethCatalogueProofDagNodeBlock313_checker, twentiethCatalogueProofDagNodeBlock314_checker, twentiethCatalogueProofDagNodeBlock315_checker, twentiethCatalogueProofDagNodeBlock316_checker, twentiethCatalogueProofDagNodeBlock317_checker, twentiethCatalogueProofDagNodeBlock318_checker, twentiethCatalogueProofDagNodeBlock319_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
