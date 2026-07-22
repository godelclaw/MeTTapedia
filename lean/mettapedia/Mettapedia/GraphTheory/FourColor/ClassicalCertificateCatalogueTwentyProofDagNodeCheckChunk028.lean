import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock224_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 224 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock225_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 225 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock226_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 226 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock227_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 227 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock228_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 228 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock229_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 229 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock230_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 230 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock231_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 231 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 028. -/
theorem twentiethCatalogueProofDagNodeChunk028_checker
    (block : Nat) (hlower : 224 ≤ block) (hupper : block < 232) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock224_checker, twentiethCatalogueProofDagNodeBlock225_checker, twentiethCatalogueProofDagNodeBlock226_checker, twentiethCatalogueProofDagNodeBlock227_checker, twentiethCatalogueProofDagNodeBlock228_checker, twentiethCatalogueProofDagNodeBlock229_checker, twentiethCatalogueProofDagNodeBlock230_checker, twentiethCatalogueProofDagNodeBlock231_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
