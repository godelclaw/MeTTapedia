import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock504_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 504 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock505_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 505 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock506_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 506 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock507_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 507 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock508_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 508 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock509_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 509 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock510_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 510 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock511_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 511 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 063. -/
theorem twentiethCatalogueProofDagNodeChunk063_checker
    (block : Nat) (hlower : 504 ≤ block) (hupper : block < 512) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock504_checker, twentiethCatalogueProofDagNodeBlock505_checker, twentiethCatalogueProofDagNodeBlock506_checker, twentiethCatalogueProofDagNodeBlock507_checker, twentiethCatalogueProofDagNodeBlock508_checker, twentiethCatalogueProofDagNodeBlock509_checker, twentiethCatalogueProofDagNodeBlock510_checker, twentiethCatalogueProofDagNodeBlock511_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
