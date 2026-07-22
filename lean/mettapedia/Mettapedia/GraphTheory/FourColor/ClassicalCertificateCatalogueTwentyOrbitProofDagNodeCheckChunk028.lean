import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock224_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 224 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock225_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 225 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock226_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 226 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock227_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 227 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock228_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 228 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock229_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 229 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock230_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 230 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock231_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 231 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 028. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk028_checker
    (block : Nat) (hlower : 224 ≤ block) (hupper : block < 232) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock224_checker,
      twentiethCatalogueOrbitProofDagNodeBlock225_checker,
      twentiethCatalogueOrbitProofDagNodeBlock226_checker,
      twentiethCatalogueOrbitProofDagNodeBlock227_checker,
      twentiethCatalogueOrbitProofDagNodeBlock228_checker,
      twentiethCatalogueOrbitProofDagNodeBlock229_checker,
      twentiethCatalogueOrbitProofDagNodeBlock230_checker,
      twentiethCatalogueOrbitProofDagNodeBlock231_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
