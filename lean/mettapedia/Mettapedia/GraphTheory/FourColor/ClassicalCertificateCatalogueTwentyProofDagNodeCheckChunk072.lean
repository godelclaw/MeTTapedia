import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock576_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 576 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock577_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 577 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock578_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 578 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock579_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 579 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock580_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 580 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock581_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 581 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock582_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 582 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock583_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 583 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 072. -/
theorem twentiethCatalogueProofDagNodeChunk072_checker
    (block : Nat) (hlower : 576 ≤ block) (hupper : block < 584) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock576_checker, twentiethCatalogueProofDagNodeBlock577_checker, twentiethCatalogueProofDagNodeBlock578_checker, twentiethCatalogueProofDagNodeBlock579_checker, twentiethCatalogueProofDagNodeBlock580_checker, twentiethCatalogueProofDagNodeBlock581_checker, twentiethCatalogueProofDagNodeBlock582_checker, twentiethCatalogueProofDagNodeBlock583_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
