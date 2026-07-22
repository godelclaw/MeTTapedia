import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock648_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 648 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock649_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 649 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock650_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 650 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock651_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 651 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock652_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 652 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock653_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 653 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock654_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 654 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock655_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 655 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 081. -/
theorem twentiethCatalogueProofDagNodeChunk081_checker
    (block : Nat) (hlower : 648 ≤ block) (hupper : block < 656) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock648_checker, twentiethCatalogueProofDagNodeBlock649_checker, twentiethCatalogueProofDagNodeBlock650_checker, twentiethCatalogueProofDagNodeBlock651_checker, twentiethCatalogueProofDagNodeBlock652_checker, twentiethCatalogueProofDagNodeBlock653_checker, twentiethCatalogueProofDagNodeBlock654_checker, twentiethCatalogueProofDagNodeBlock655_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
