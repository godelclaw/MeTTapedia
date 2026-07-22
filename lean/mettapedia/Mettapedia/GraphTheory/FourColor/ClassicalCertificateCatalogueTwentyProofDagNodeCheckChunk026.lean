import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock208_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 208 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock209_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 209 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock210_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 210 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock211_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 211 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock212_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 212 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock213_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 213 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock214_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 214 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock215_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 215 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 026. -/
theorem twentiethCatalogueProofDagNodeChunk026_checker
    (block : Nat) (hlower : 208 ≤ block) (hupper : block < 216) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock208_checker, twentiethCatalogueProofDagNodeBlock209_checker, twentiethCatalogueProofDagNodeBlock210_checker, twentiethCatalogueProofDagNodeBlock211_checker, twentiethCatalogueProofDagNodeBlock212_checker, twentiethCatalogueProofDagNodeBlock213_checker, twentiethCatalogueProofDagNodeBlock214_checker, twentiethCatalogueProofDagNodeBlock215_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
