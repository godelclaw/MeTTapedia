import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock416_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 416 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock417_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 417 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock418_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 418 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock419_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 419 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock420_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 420 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock421_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 421 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock422_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 422 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock423_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 423 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 052. -/
theorem twentiethCatalogueProofDagNodeChunk052_checker
    (block : Nat) (hlower : 416 ≤ block) (hupper : block < 424) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock416_checker, twentiethCatalogueProofDagNodeBlock417_checker, twentiethCatalogueProofDagNodeBlock418_checker, twentiethCatalogueProofDagNodeBlock419_checker, twentiethCatalogueProofDagNodeBlock420_checker, twentiethCatalogueProofDagNodeBlock421_checker, twentiethCatalogueProofDagNodeBlock422_checker, twentiethCatalogueProofDagNodeBlock423_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
