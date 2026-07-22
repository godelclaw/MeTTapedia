import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock024_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 24 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock025_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 25 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock026_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 26 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock027_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 27 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock028_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 28 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock029_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 29 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock030_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 30 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock031_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 31 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 003. -/
theorem twentiethCatalogueProofDagNodeChunk003_checker
    (block : Nat) (hlower : 24 ≤ block) (hupper : block < 32) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock024_checker, twentiethCatalogueProofDagNodeBlock025_checker, twentiethCatalogueProofDagNodeBlock026_checker, twentiethCatalogueProofDagNodeBlock027_checker, twentiethCatalogueProofDagNodeBlock028_checker, twentiethCatalogueProofDagNodeBlock029_checker, twentiethCatalogueProofDagNodeBlock030_checker, twentiethCatalogueProofDagNodeBlock031_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
