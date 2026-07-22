import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock192_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 192 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock193_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 193 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock194_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 194 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock195_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 195 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock196_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 196 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock197_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 197 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock198_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 198 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock199_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 199 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 024. -/
theorem twentiethCatalogueProofDagNodeChunk024_checker
    (block : Nat) (hlower : 192 ≤ block) (hupper : block < 200) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock192_checker, twentiethCatalogueProofDagNodeBlock193_checker, twentiethCatalogueProofDagNodeBlock194_checker, twentiethCatalogueProofDagNodeBlock195_checker, twentiethCatalogueProofDagNodeBlock196_checker, twentiethCatalogueProofDagNodeBlock197_checker, twentiethCatalogueProofDagNodeBlock198_checker, twentiethCatalogueProofDagNodeBlock199_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
