import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock192_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 192 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock193_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 193 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock194_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 194 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock195_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 195 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock196_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 196 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock197_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 197 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock198_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 198 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock199_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 199 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 024. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk024_checker
    (block : Nat) (hlower : 192 ≤ block) (hupper : block < 200) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock192_checker,
      twentiethCatalogueOrbitProofDagNodeBlock193_checker,
      twentiethCatalogueOrbitProofDagNodeBlock194_checker,
      twentiethCatalogueOrbitProofDagNodeBlock195_checker,
      twentiethCatalogueOrbitProofDagNodeBlock196_checker,
      twentiethCatalogueOrbitProofDagNodeBlock197_checker,
      twentiethCatalogueOrbitProofDagNodeBlock198_checker,
      twentiethCatalogueOrbitProofDagNodeBlock199_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
