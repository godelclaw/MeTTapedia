import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock368_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 368 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock369_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 369 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock370_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 370 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock371_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 371 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock372_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 372 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock373_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 373 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock374_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 374 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock375_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 375 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 046. -/
theorem twentiethCatalogueProofDagNodeChunk046_checker
    (block : Nat) (hlower : 368 ≤ block) (hupper : block < 376) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock368_checker, twentiethCatalogueProofDagNodeBlock369_checker, twentiethCatalogueProofDagNodeBlock370_checker, twentiethCatalogueProofDagNodeBlock371_checker, twentiethCatalogueProofDagNodeBlock372_checker, twentiethCatalogueProofDagNodeBlock373_checker, twentiethCatalogueProofDagNodeBlock374_checker, twentiethCatalogueProofDagNodeBlock375_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
