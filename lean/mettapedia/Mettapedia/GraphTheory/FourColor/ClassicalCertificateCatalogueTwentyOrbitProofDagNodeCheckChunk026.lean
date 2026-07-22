import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock208_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 208 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock209_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 209 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock210_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 210 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock211_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 211 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock212_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 212 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock213_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 213 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock214_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 214 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock215_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 215 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 026. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk026_checker
    (block : Nat) (hlower : 208 ≤ block) (hupper : block < 216) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock208_checker,
      twentiethCatalogueOrbitProofDagNodeBlock209_checker,
      twentiethCatalogueOrbitProofDagNodeBlock210_checker,
      twentiethCatalogueOrbitProofDagNodeBlock211_checker,
      twentiethCatalogueOrbitProofDagNodeBlock212_checker,
      twentiethCatalogueOrbitProofDagNodeBlock213_checker,
      twentiethCatalogueOrbitProofDagNodeBlock214_checker,
      twentiethCatalogueOrbitProofDagNodeBlock215_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
