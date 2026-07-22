import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock200_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 200 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock201_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 201 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock202_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 202 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock203_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 203 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock204_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 204 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock205_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 205 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock206_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 206 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock207_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 207 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 025. -/
theorem twentiethCatalogueProofDagNodeChunk025_checker
    (block : Nat) (hlower : 200 ≤ block) (hupper : block < 208) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock200_checker, twentiethCatalogueProofDagNodeBlock201_checker, twentiethCatalogueProofDagNodeBlock202_checker, twentiethCatalogueProofDagNodeBlock203_checker, twentiethCatalogueProofDagNodeBlock204_checker, twentiethCatalogueProofDagNodeBlock205_checker, twentiethCatalogueProofDagNodeBlock206_checker, twentiethCatalogueProofDagNodeBlock207_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
