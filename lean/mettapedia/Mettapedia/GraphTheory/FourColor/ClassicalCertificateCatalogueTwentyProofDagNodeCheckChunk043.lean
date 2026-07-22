import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock344_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 344 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock345_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 345 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock346_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 346 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock347_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 347 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock348_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 348 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock349_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 349 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock350_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 350 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock351_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 351 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 043. -/
theorem twentiethCatalogueProofDagNodeChunk043_checker
    (block : Nat) (hlower : 344 ≤ block) (hupper : block < 352) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock344_checker, twentiethCatalogueProofDagNodeBlock345_checker, twentiethCatalogueProofDagNodeBlock346_checker, twentiethCatalogueProofDagNodeBlock347_checker, twentiethCatalogueProofDagNodeBlock348_checker, twentiethCatalogueProofDagNodeBlock349_checker, twentiethCatalogueProofDagNodeBlock350_checker, twentiethCatalogueProofDagNodeBlock351_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
