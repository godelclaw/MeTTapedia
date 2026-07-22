import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock168_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 168 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock169_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 169 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock170_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 170 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock171_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 171 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock172_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 172 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock173_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 173 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock174_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 174 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock175_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 175 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 021. -/
theorem twentiethCatalogueProofDagNodeChunk021_checker
    (block : Nat) (hlower : 168 ≤ block) (hupper : block < 176) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock168_checker, twentiethCatalogueProofDagNodeBlock169_checker, twentiethCatalogueProofDagNodeBlock170_checker, twentiethCatalogueProofDagNodeBlock171_checker, twentiethCatalogueProofDagNodeBlock172_checker, twentiethCatalogueProofDagNodeBlock173_checker, twentiethCatalogueProofDagNodeBlock174_checker, twentiethCatalogueProofDagNodeBlock175_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
