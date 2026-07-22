import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock616_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 616 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock617_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 617 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock618_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 618 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock619_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 619 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock620_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 620 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock621_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 621 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock622_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 622 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock623_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 623 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 077. -/
theorem twentiethCatalogueProofDagNodeChunk077_checker
    (block : Nat) (hlower : 616 ≤ block) (hupper : block < 624) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock616_checker, twentiethCatalogueProofDagNodeBlock617_checker, twentiethCatalogueProofDagNodeBlock618_checker, twentiethCatalogueProofDagNodeBlock619_checker, twentiethCatalogueProofDagNodeBlock620_checker, twentiethCatalogueProofDagNodeBlock621_checker, twentiethCatalogueProofDagNodeBlock622_checker, twentiethCatalogueProofDagNodeBlock623_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
