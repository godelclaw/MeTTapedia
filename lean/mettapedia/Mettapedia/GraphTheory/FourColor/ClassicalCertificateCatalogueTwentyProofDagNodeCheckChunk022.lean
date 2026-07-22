import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock176_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 176 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock177_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 177 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock178_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 178 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock179_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 179 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock180_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 180 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock181_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 181 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock182_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 182 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock183_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 183 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 022. -/
theorem twentiethCatalogueProofDagNodeChunk022_checker
    (block : Nat) (hlower : 176 ≤ block) (hupper : block < 184) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock176_checker, twentiethCatalogueProofDagNodeBlock177_checker, twentiethCatalogueProofDagNodeBlock178_checker, twentiethCatalogueProofDagNodeBlock179_checker, twentiethCatalogueProofDagNodeBlock180_checker, twentiethCatalogueProofDagNodeBlock181_checker, twentiethCatalogueProofDagNodeBlock182_checker, twentiethCatalogueProofDagNodeBlock183_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
