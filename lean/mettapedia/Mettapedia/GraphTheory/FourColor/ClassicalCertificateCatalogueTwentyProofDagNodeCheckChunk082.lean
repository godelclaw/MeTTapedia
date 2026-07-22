import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock656_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 656 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock657_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 657 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock658_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 658 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock659_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 659 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock660_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 660 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock661_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 661 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock662_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 662 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock663_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 663 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 082. -/
theorem twentiethCatalogueProofDagNodeChunk082_checker
    (block : Nat) (hlower : 656 ≤ block) (hupper : block < 664) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock656_checker, twentiethCatalogueProofDagNodeBlock657_checker, twentiethCatalogueProofDagNodeBlock658_checker, twentiethCatalogueProofDagNodeBlock659_checker, twentiethCatalogueProofDagNodeBlock660_checker, twentiethCatalogueProofDagNodeBlock661_checker, twentiethCatalogueProofDagNodeBlock662_checker, twentiethCatalogueProofDagNodeBlock663_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
