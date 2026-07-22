import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock160_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 160 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock161_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 161 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock162_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 162 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock163_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 163 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock164_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 164 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock165_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 165 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock166_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 166 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock167_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 167 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 020. -/
theorem twentiethCatalogueProofDagNodeChunk020_checker
    (block : Nat) (hlower : 160 ≤ block) (hupper : block < 168) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock160_checker, twentiethCatalogueProofDagNodeBlock161_checker, twentiethCatalogueProofDagNodeBlock162_checker, twentiethCatalogueProofDagNodeBlock163_checker, twentiethCatalogueProofDagNodeBlock164_checker, twentiethCatalogueProofDagNodeBlock165_checker, twentiethCatalogueProofDagNodeBlock166_checker, twentiethCatalogueProofDagNodeBlock167_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
